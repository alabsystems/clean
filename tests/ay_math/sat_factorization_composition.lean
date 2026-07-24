-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained SAT-COMP math smoke package.
-- Minimal Church encodings avoid depending on staged imports.

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

def AyDuplicateCnf (sub : Prop) (left : Prop) (right : Prop) :=
  AyConj sub (AyConj left (AyConj sub right))

def AyFactoredCnf (sub : Prop) (left : Prop) (right : Prop) :=
  AyConj sub (AyConj left right)

theorem ay_duplicate_subconstraint_factor_forward
    (sub : Prop) (left : Prop) (right : Prop) :
    AyDuplicateCnf sub left right ->
    AyFactoredCnf sub left right := by
  intro original
  intro result
  intro build
  exact original result
    (fun hsub tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hsubAgain hright =>
              build hsub (ay_conj_intro left right hleft hright))))

theorem ay_duplicate_subconstraint_factor_backward
    (sub : Prop) (left : Prop) (right : Prop) :
    AyFactoredCnf sub left right ->
    AyDuplicateCnf sub left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hsub tail =>
      tail result
        (fun hleft hright =>
          build hsub
            (ay_conj_intro left (AyConj sub right) hleft
              (ay_conj_intro sub right hsub hright))))

theorem ay_duplicate_subconstraint_factor_equisat
    (sub : Prop) (left : Prop) (right : Prop) :
    AyEquisat
      (AyDuplicateCnf sub left right)
      (AyFactoredCnf sub left right) := by
  exact ay_conj_intro
    (AyDuplicateCnf sub left right -> AyFactoredCnf sub left right)
    (AyFactoredCnf sub left right -> AyDuplicateCnf sub left right)
    (ay_duplicate_subconstraint_factor_forward sub left right)
    (ay_duplicate_subconstraint_factor_backward sub left right)

def AyTwoDuplicateBlocks
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :=
  AyConj
    (AyDuplicateCnf subA leftA rightA)
    (AyConj (AyDuplicateCnf subB leftB rightB) rest)

def AyFirstBlockFactored
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :=
  AyConj
    (AyFactoredCnf subA leftA rightA)
    (AyConj (AyDuplicateCnf subB leftB rightB) rest)

def AyTwoFactoredBlocks
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :=
  AyConj
    (AyFactoredCnf subA leftA rightA)
    (AyConj (AyFactoredCnf subB leftB rightB) rest)

theorem ay_first_duplicate_block_factor_forward
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest ->
    AyFirstBlockFactored subA leftA rightA subB leftB rightB rest := by
  intro original
  intro result
  intro build
  exact original result
    (fun blockA tail =>
      build
        (ay_duplicate_subconstraint_factor_forward subA leftA rightA blockA)
        tail)

theorem ay_first_duplicate_block_factor_backward
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyFirstBlockFactored subA leftA rightA subB leftB rightB rest ->
    AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest := by
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun blockA tail =>
      build
        (ay_duplicate_subconstraint_factor_backward subA leftA rightA blockA)
        tail)

theorem ay_first_duplicate_block_factor_equisat
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyEquisat
      (AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest)
      (AyFirstBlockFactored subA leftA rightA subB leftB rightB rest) := by
  exact ay_conj_intro
    (AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest ->
      AyFirstBlockFactored subA leftA rightA subB leftB rightB rest)
    (AyFirstBlockFactored subA leftA rightA subB leftB rightB rest ->
      AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest)
    (ay_first_duplicate_block_factor_forward
      subA leftA rightA subB leftB rightB rest)
    (ay_first_duplicate_block_factor_backward
      subA leftA rightA subB leftB rightB rest)

theorem ay_second_duplicate_block_factor_forward
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyFirstBlockFactored subA leftA rightA subB leftB rightB rest ->
    AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest := by
  intro original
  intro result
  intro build
  exact original result
    (fun blockA tail =>
      tail result
        (fun blockB hrest =>
          build blockA
            (ay_conj_intro
              (AyFactoredCnf subB leftB rightB)
              rest
              (ay_duplicate_subconstraint_factor_forward subB leftB rightB blockB)
              hrest)))

theorem ay_second_duplicate_block_factor_backward
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest ->
    AyFirstBlockFactored subA leftA rightA subB leftB rightB rest := by
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun blockA tail =>
      tail result
        (fun blockB hrest =>
          build blockA
            (ay_conj_intro
              (AyDuplicateCnf subB leftB rightB)
              rest
              (ay_duplicate_subconstraint_factor_backward subB leftB rightB blockB)
              hrest)))

theorem ay_second_duplicate_block_factor_equisat
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyEquisat
      (AyFirstBlockFactored subA leftA rightA subB leftB rightB rest)
      (AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest) := by
  exact ay_conj_intro
    (AyFirstBlockFactored subA leftA rightA subB leftB rightB rest ->
      AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest)
    (AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest ->
      AyFirstBlockFactored subA leftA rightA subB leftB rightB rest)
    (ay_second_duplicate_block_factor_forward
      subA leftA rightA subB leftB rightB rest)
    (ay_second_duplicate_block_factor_backward
      subA leftA rightA subB leftB rightB rest)

theorem ay_two_duplicate_blocks_factor_equisat
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (rest : Prop) :
    AyEquisat
      (AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest)
      (AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest) := by
  exact ay_conj_intro
    (AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest ->
      AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest)
    (AyTwoFactoredBlocks subA leftA rightA subB leftB rightB rest ->
      AyTwoDuplicateBlocks subA leftA rightA subB leftB rightB rest)
    (fun original =>
      ay_second_duplicate_block_factor_forward
        subA leftA rightA subB leftB rightB rest
        (ay_first_duplicate_block_factor_forward
          subA leftA rightA subB leftB rightB rest
          original))
    (fun transformed =>
      ay_first_duplicate_block_factor_backward
        subA leftA rightA subB leftB rightB rest
        (ay_second_duplicate_block_factor_backward
          subA leftA rightA subB leftB rightB rest
          transformed))
