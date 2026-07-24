-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for circuit factorization followed by a
-- commander-style AMO extension over auxiliary gates. The commander extension
-- is guarded by an explicit side condition from the factored circuit formula.

def AyCFCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyCFCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCFCEquisat (original : Prop) (transformed : Prop) :=
  AyCFCConj (original -> transformed) (transformed -> original)

def AyCFCDuplicateBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyCFCConj gate (AyCFCConj left (AyCFCConj gate right))

def AyCFCFactoredBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyCFCConj gate (AyCFCConj left right)

def AyCFCOriginal
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFCDuplicateBlock
    (AyCFCDuplicateBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFCSubgatesFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFCDuplicateBlock
    (AyCFCFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFCParentsFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFCFactoredBlock
    (AyCFCFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFCCommanderAux2Cnf
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :=
  AyCFCConj
    (AyCFCDisj (Not auxA) (Not auxB))
    (AyCFCConj
      (AyCFCDisj (Not auxA) cmd)
      (AyCFCDisj (Not auxB) cmd))

def AyCFCCommanderFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop)
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :=
  AyCFCConj
    (AyCFCParentsFactored sub subLeft subRight parentLeft parentRight)
    (AyCFCCommanderAux2Cnf auxA auxB cmd)

def AyCFCCommanderSideCondition
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop)
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :=
  AyCFCParentsFactored sub subLeft subRight parentLeft parentRight ->
  AyCFCCommanderAux2Cnf auxA auxB cmd

theorem ay_cfc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCFCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_cfc_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyCFCEquisat original transformed := by
  intro forward
  intro backward
  exact ay_cfc_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_cfc_pair_clause_forbids_both
    (p : Prop) (q : Prop) :
    AyCFCDisj (Not p) (Not q) -> p -> q -> False := by
  intro pair_clause
  intro hp
  intro hq
  exact pair_clause False
    (fun not_p => not_p hp)
    (fun not_q => not_q hq)

theorem ay_cfc_guard_clause_implies_commander
    (lit : Prop) (cmd : Prop) :
    AyCFCDisj (Not lit) cmd -> lit -> cmd := by
  intro guard
  intro hlit
  exact guard cmd
    (fun not_lit => False.elim (not_lit hlit))
    (fun hcmd => hcmd)

theorem ay_cfc_commander_aux_forbids_both
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyCFCCommanderAux2Cnf auxA auxB cmd ->
    auxA -> auxB -> False := by
  intro commander
  intro hauxA
  intro hauxB
  exact commander False
    (fun pair_clause _guards =>
      ay_cfc_pair_clause_forbids_both auxA auxB pair_clause hauxA hauxB)

theorem ay_cfc_commander_auxA_implies_cmd
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyCFCCommanderAux2Cnf auxA auxB cmd ->
    auxA -> cmd := by
  intro commander
  intro hauxA
  exact commander cmd
    (fun _pair_clause guards =>
      guards cmd
        (fun auxA_guard _auxB_guard =>
          ay_cfc_guard_clause_implies_commander auxA cmd auxA_guard hauxA))

theorem ay_cfc_commander_auxB_implies_cmd
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyCFCCommanderAux2Cnf auxA auxB cmd ->
    auxB -> cmd := by
  intro commander
  intro hauxB
  exact commander cmd
    (fun _pair_clause guards =>
      guards cmd
        (fun _auxA_guard auxB_guard =>
          ay_cfc_guard_clause_implies_commander auxB cmd auxB_guard hauxB))

theorem ay_cfc_duplicate_project
    (gate : Prop) (left : Prop) (right : Prop) :
    AyCFCDuplicateBlock gate left right ->
    AyCFCFactoredBlock gate left right := by
  intro duplicated
  intro result
  intro build
  exact duplicated result
    (fun hgate tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hgate_again hright =>
              build hgate (ay_cfc_conj_intro left right hleft hright))))

theorem ay_cfc_duplicate_reconstruct
    (gate : Prop) (left : Prop) (right : Prop) :
    AyCFCFactoredBlock gate left right ->
    AyCFCDuplicateBlock gate left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hgate tail =>
      tail result
        (fun hleft hright =>
          build hgate
            (ay_cfc_conj_intro
              left
              (AyCFCConj gate right)
              hleft
              (ay_cfc_conj_intro gate right hgate hright))))

theorem ay_cfc_subgates_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFCOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFCSubgatesFactored sub subLeft subRight parentLeft parentRight := by
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
                (ay_cfc_duplicate_project sub subLeft subRight parentGate)
                (ay_cfc_conj_intro
                  parentLeft
                  (AyCFCConj
                    (AyCFCFactoredBlock sub subLeft subRight)
                    parentRight)
                  hparentLeft
                  (ay_cfc_conj_intro
                    (AyCFCFactoredBlock sub subLeft subRight)
                    parentRight
                    (ay_cfc_duplicate_project
                      sub subLeft subRight parentGateAgain)
                    hparentRight)))))

theorem ay_cfc_subgates_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFCSubgatesFactored sub subLeft subRight parentLeft parentRight ->
    AyCFCOriginal sub subLeft subRight parentLeft parentRight := by
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
                (ay_cfc_duplicate_reconstruct sub subLeft subRight parentGate)
                (ay_cfc_conj_intro
                  parentLeft
                  (AyCFCConj
                    (AyCFCDuplicateBlock sub subLeft subRight)
                    parentRight)
                  hparentLeft
                  (ay_cfc_conj_intro
                    (AyCFCDuplicateBlock sub subLeft subRight)
                    parentRight
                    (ay_cfc_duplicate_reconstruct
                      sub subLeft subRight parentGateAgain)
                    hparentRight)))))

theorem ay_cfc_parent_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFCSubgatesFactored sub subLeft subRight parentLeft parentRight ->
    AyCFCParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cfc_duplicate_project
    (AyCFCFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight
    transformed

theorem ay_cfc_parent_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFCParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFCSubgatesFactored sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cfc_duplicate_reconstruct
    (AyCFCFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight
    transformed

theorem ay_cfc_two_level_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFCOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFCParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro original
  exact ay_cfc_parent_project sub subLeft subRight parentLeft parentRight
    (ay_cfc_subgates_project
      sub subLeft subRight parentLeft parentRight original)

theorem ay_cfc_two_level_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFCParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFCOriginal sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cfc_subgates_reconstruct
    sub subLeft subRight parentLeft parentRight
    (ay_cfc_parent_reconstruct
      sub subLeft subRight parentLeft parentRight transformed)

theorem ay_cfc_factor_then_commander_forward
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop)
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyCFCCommanderSideCondition
      sub subLeft subRight parentLeft parentRight auxA auxB cmd ->
    AyCFCOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFCCommanderFactored
      sub subLeft subRight parentLeft parentRight auxA auxB cmd := by
  intro commander_side
  intro original
  exact ay_cfc_conj_intro
    (AyCFCParentsFactored sub subLeft subRight parentLeft parentRight)
    (AyCFCCommanderAux2Cnf auxA auxB cmd)
    (ay_cfc_two_level_project
      sub subLeft subRight parentLeft parentRight original)
    (commander_side
      (ay_cfc_two_level_project
        sub subLeft subRight parentLeft parentRight original))

theorem ay_cfc_factor_then_commander_backward
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop)
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyCFCCommanderFactored
      sub subLeft subRight parentLeft parentRight auxA auxB cmd ->
    AyCFCOriginal sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact transformed
    (AyCFCOriginal sub subLeft subRight parentLeft parentRight)
    (fun factored _commander =>
      ay_cfc_two_level_reconstruct
        sub subLeft subRight parentLeft parentRight factored)

theorem ay_cfc_factor_then_commander_equisat
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop)
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyCFCCommanderSideCondition
      sub subLeft subRight parentLeft parentRight auxA auxB cmd ->
    AyCFCEquisat
      (AyCFCOriginal sub subLeft subRight parentLeft parentRight)
      (AyCFCCommanderFactored
        sub subLeft subRight parentLeft parentRight auxA auxB cmd) := by
  intro commander_side
  exact ay_cfc_equisat_intro
    (AyCFCOriginal sub subLeft subRight parentLeft parentRight)
    (AyCFCCommanderFactored
      sub subLeft subRight parentLeft parentRight auxA auxB cmd)
    (ay_cfc_factor_then_commander_forward
      sub subLeft subRight parentLeft parentRight auxA auxB cmd
      commander_side)
    (ay_cfc_factor_then_commander_backward
      sub subLeft subRight parentLeft parentRight auxA auxB cmd)
