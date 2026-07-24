-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for composing two SAT vivification /
-- asymmetric branch-pruning steps. The first step replaces
-- `lit1 OR (lit2 OR final)` by `lit2 OR final`; the second replaces
-- `lit2 OR final` by `final`, under the same remaining formula.

def AyVivChainDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyVivChainConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyVivChainEquisat (original : Prop) (transformed : Prop) :=
  AyVivChainConj (original -> transformed) (transformed -> original)

def AyVivChainOriginal
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :=
  AyVivChainConj (AyVivChainDisj lit1 (AyVivChainDisj lit2 final)) rest

def AyVivChainMiddle
    (lit2 : Prop) (final : Prop) (rest : Prop) :=
  AyVivChainConj (AyVivChainDisj lit2 final) rest

def AyVivChainPruned
    (final : Prop) (rest : Prop) :=
  AyVivChainConj final rest

def AyVivChainStepOneSide
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :=
  lit1 -> rest -> AyVivChainDisj lit2 final

def AyVivChainStepTwoSide
    (lit2 : Prop) (final : Prop) (rest : Prop) :=
  lit2 -> rest -> final

def AyVivChainComposedSide
    (lit1 : Prop) (final : Prop) (rest : Prop) :=
  lit1 -> rest -> final

theorem ay_viv_chain_disj_right
    (p : Prop) (q : Prop) :
    q -> AyVivChainDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_viv_chain_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyVivChainConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_viv_chain_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyVivChainEquisat original transformed := by
  intro forward
  intro backward
  exact ay_viv_chain_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_viv_chain_side_condition_compose
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainStepOneSide lit1 lit2 final rest ->
    AyVivChainStepTwoSide lit2 final rest ->
    AyVivChainComposedSide lit1 final rest := by
  intro first_branch
  intro second_branch
  intro hlit1
  intro hrest
  exact first_branch hlit1 hrest final
    (fun hlit2 => second_branch hlit2 hrest)
    (fun hfinal => hfinal)

theorem ay_viv_chain_first_forward
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainStepOneSide lit1 lit2 final rest ->
    AyVivChainOriginal lit1 lit2 final rest ->
    AyVivChainMiddle lit2 final rest := by
  intro first_branch
  intro original
  intro result
  intro build
  exact original result
    (fun clause hrest =>
      clause result
        (fun hlit1 => build (first_branch hlit1 hrest) hrest)
        (fun tail => build tail hrest))

theorem ay_viv_chain_first_backward
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainMiddle lit2 final rest ->
    AyVivChainOriginal lit1 lit2 final rest := by
  intro middle
  intro result
  intro build
  exact middle result
    (fun tail hrest =>
      build
        (ay_viv_chain_disj_right lit1 (AyVivChainDisj lit2 final) tail)
        hrest)

theorem ay_viv_chain_second_forward
    (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainStepTwoSide lit2 final rest ->
    AyVivChainMiddle lit2 final rest ->
    AyVivChainPruned final rest := by
  intro second_branch
  intro middle
  intro result
  intro build
  exact middle result
    (fun tail hrest =>
      tail result
        (fun hlit2 => build (second_branch hlit2 hrest) hrest)
        (fun hfinal => build hfinal hrest))

theorem ay_viv_chain_second_backward
    (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainPruned final rest ->
    AyVivChainMiddle lit2 final rest := by
  intro pruned
  intro result
  intro build
  exact pruned result
    (fun hfinal hrest =>
      build
        (ay_viv_chain_disj_right lit2 final hfinal)
        hrest)

theorem ay_viv_chain_forward
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainStepOneSide lit1 lit2 final rest ->
    AyVivChainStepTwoSide lit2 final rest ->
    AyVivChainOriginal lit1 lit2 final rest ->
    AyVivChainPruned final rest := by
  intro first_branch
  intro second_branch
  intro original
  exact ay_viv_chain_second_forward lit2 final rest second_branch
    (ay_viv_chain_first_forward lit1 lit2 final rest first_branch original)

theorem ay_viv_chain_backward
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainPruned final rest ->
    AyVivChainOriginal lit1 lit2 final rest := by
  intro pruned
  exact ay_viv_chain_first_backward lit1 lit2 final rest
    (ay_viv_chain_second_backward lit2 final rest pruned)

theorem ay_viv_chain_equisat
    (lit1 : Prop) (lit2 : Prop) (final : Prop) (rest : Prop) :
    AyVivChainStepOneSide lit1 lit2 final rest ->
    AyVivChainStepTwoSide lit2 final rest ->
    AyVivChainEquisat
      (AyVivChainOriginal lit1 lit2 final rest)
      (AyVivChainPruned final rest) := by
  intro first_branch
  intro second_branch
  exact ay_viv_chain_equisat_intro
    (AyVivChainOriginal lit1 lit2 final rest)
    (AyVivChainPruned final rest)
    (ay_viv_chain_forward lit1 lit2 final rest first_branch second_branch)
    (ay_viv_chain_backward lit1 lit2 final rest)
