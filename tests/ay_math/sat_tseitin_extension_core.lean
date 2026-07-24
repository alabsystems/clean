-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for Tseitin/auxiliary-variable definitional extension.
-- This file stays self-contained and uses the same Church encodings as
-- sat_comp_transform_core.lean.

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyEquiv (p : Prop) (q : Prop) :=
  AyConj (p -> q) (q -> p)

def AyRepeatedSubformulaFormula
    (sub : Prop) (leftContext : Prop) (rightContext : Prop) :=
  AyConj sub (AyConj leftContext (AyConj sub rightContext))

def AyTseitinAuxFormula
    (aux : Prop) (leftAuxContext : Prop) (rightAuxContext : Prop) :=
  AyConj aux (AyConj leftAuxContext (AyConj aux rightAuxContext))

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_equiv_forward
    (p : Prop) (q : Prop) :
    AyEquiv p q -> p -> q := by
  intro equiv
  exact equiv (p -> q) (fun forward _backward => forward)

theorem ay_equiv_backward
    (p : Prop) (q : Prop) :
    AyEquiv p q -> q -> p := by
  intro equiv
  exact equiv (q -> p) (fun _forward backward => backward)

theorem ay_tseitin_projection_replaces_aux_by_sub
    (sub : Prop) (aux : Prop)
    (leftSubContext : Prop) (rightSubContext : Prop) :
    AyEquiv aux sub ->
    AyTseitinAuxFormula aux leftSubContext rightSubContext ->
    AyRepeatedSubformulaFormula sub leftSubContext rightSubContext := by
  intro aux_equiv_sub
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun auxSat tail =>
      tail result
        (fun leftSat tail2 =>
          tail2 result
            (fun _auxSatAgain rightSat =>
              build
                (ay_equiv_forward aux sub aux_equiv_sub auxSat)
                (ay_conj_intro leftSubContext (AyConj sub rightSubContext)
                  leftSat
                  (ay_conj_intro sub rightSubContext
                    (ay_equiv_forward aux sub aux_equiv_sub auxSat)
                    rightSat)))))

theorem ay_tseitin_extension_replaces_sub_by_aux
    (sub : Prop) (aux : Prop)
    (leftAuxContext : Prop) (rightAuxContext : Prop) :
    AyEquiv aux sub ->
    AyRepeatedSubformulaFormula sub leftAuxContext rightAuxContext ->
    AyTseitinAuxFormula aux leftAuxContext rightAuxContext := by
  intro aux_equiv_sub
  intro original
  intro result
  intro build
  exact original result
    (fun subSat tail =>
      tail result
        (fun leftSat tail2 =>
          tail2 result
            (fun _subSatAgain rightSat =>
              build
                (ay_equiv_backward aux sub aux_equiv_sub subSat)
                (ay_conj_intro leftAuxContext (AyConj aux rightAuxContext)
                  leftSat
                  (ay_conj_intro aux rightAuxContext
                    (ay_equiv_backward aux sub aux_equiv_sub subSat)
                    rightSat)))))

theorem ay_tseitin_repeated_subformula_equisat
    (sub : Prop) (aux : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux sub ->
    AyEquisat
      (AyRepeatedSubformulaFormula sub leftContext rightContext)
      (AyTseitinAuxFormula aux leftContext rightContext) := by
  intro aux_equiv_sub
  exact ay_conj_intro
    (AyRepeatedSubformulaFormula sub leftContext rightContext ->
      AyTseitinAuxFormula aux leftContext rightContext)
    (AyTseitinAuxFormula aux leftContext rightContext ->
      AyRepeatedSubformulaFormula sub leftContext rightContext)
    (ay_tseitin_extension_replaces_sub_by_aux
      sub aux leftContext rightContext aux_equiv_sub)
    (ay_tseitin_projection_replaces_aux_by_sub
      sub aux leftContext rightContext aux_equiv_sub)

theorem ay_tseitin_extension_direction
    (sub : Prop) (aux : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux sub ->
    AyRepeatedSubformulaFormula sub leftContext rightContext ->
    AyTseitinAuxFormula aux leftContext rightContext := by
  intro aux_equiv_sub
  exact ay_tseitin_extension_replaces_sub_by_aux
    sub aux leftContext rightContext aux_equiv_sub

theorem ay_tseitin_projection_direction
    (sub : Prop) (aux : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux sub ->
    AyTseitinAuxFormula aux leftContext rightContext ->
    AyRepeatedSubformulaFormula sub leftContext rightContext := by
  intro aux_equiv_sub
  exact ay_tseitin_projection_replaces_aux_by_sub
    sub aux leftContext rightContext aux_equiv_sub
