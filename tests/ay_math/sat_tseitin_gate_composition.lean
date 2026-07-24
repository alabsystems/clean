-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for composing Tseitin auxiliary gate definitions.
-- The package is self-contained and uses Church encodings, matching the
-- SAT-COMP-facing theorem style in sat_comp_transform_core.lean.

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyEquiv (p : Prop) (q : Prop) :=
  AyConj (p -> q) (q -> p)

def AyGateFormula
    (gate : Prop) (leftContext : Prop) (rightContext : Prop) :=
  AyConj gate (AyConj leftContext (AyConj gate rightContext))

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

theorem ay_gate_equiv_projection
    (sourceGate : Prop) (targetGate : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv sourceGate targetGate ->
    AyGateFormula sourceGate leftContext rightContext ->
    AyGateFormula targetGate leftContext rightContext := by
  intro gate_equiv
  intro sourceFormula
  intro result
  intro build
  exact sourceFormula result
    (fun sourceSat tail =>
      tail result
        (fun leftSat tail2 =>
          tail2 result
            (fun _sourceSatAgain rightSat =>
              build
                (ay_equiv_forward sourceGate targetGate gate_equiv sourceSat)
                (ay_conj_intro leftContext (AyConj targetGate rightContext)
                  leftSat
                  (ay_conj_intro targetGate rightContext
                    (ay_equiv_forward sourceGate targetGate
                      gate_equiv sourceSat)
                    rightSat)))))

theorem ay_gate_equiv_extension
    (sourceGate : Prop) (targetGate : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv sourceGate targetGate ->
    AyGateFormula targetGate leftContext rightContext ->
    AyGateFormula sourceGate leftContext rightContext := by
  intro gate_equiv
  intro targetFormula
  intro result
  intro build
  exact targetFormula result
    (fun targetSat tail =>
      tail result
        (fun leftSat tail2 =>
          tail2 result
            (fun _targetSatAgain rightSat =>
              build
                (ay_equiv_backward sourceGate targetGate
                  gate_equiv targetSat)
                (ay_conj_intro leftContext (AyConj sourceGate rightContext)
                  leftSat
                  (ay_conj_intro sourceGate rightContext
                    (ay_equiv_backward sourceGate targetGate
                      gate_equiv targetSat)
                    rightSat)))))

theorem ay_tseitin_gate_projection_aux2_aux1_sub
    (sub : Prop) (aux1 : Prop) (aux2 : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux1 sub ->
    AyEquiv aux2 aux1 ->
    AyGateFormula aux2 leftContext rightContext ->
    AyGateFormula sub leftContext rightContext := by
  intro aux1_equiv_sub
  intro aux2_equiv_aux1
  intro aux2Formula
  exact ay_gate_equiv_projection aux1 sub leftContext rightContext
    aux1_equiv_sub
    (ay_gate_equiv_projection aux2 aux1 leftContext rightContext
      aux2_equiv_aux1 aux2Formula)

theorem ay_tseitin_gate_extension_sub_aux1_aux2
    (sub : Prop) (aux1 : Prop) (aux2 : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux1 sub ->
    AyEquiv aux2 aux1 ->
    AyGateFormula sub leftContext rightContext ->
    AyGateFormula aux2 leftContext rightContext := by
  intro aux1_equiv_sub
  intro aux2_equiv_aux1
  intro subFormula
  exact ay_gate_equiv_extension aux2 aux1 leftContext rightContext
    aux2_equiv_aux1
    (ay_gate_equiv_extension aux1 sub leftContext rightContext
      aux1_equiv_sub subFormula)

theorem ay_tseitin_gate_composition_equisat
    (sub : Prop) (aux1 : Prop) (aux2 : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux1 sub ->
    AyEquiv aux2 aux1 ->
    AyEquisat
      (AyGateFormula sub leftContext rightContext)
      (AyGateFormula aux2 leftContext rightContext) := by
  intro aux1_equiv_sub
  intro aux2_equiv_aux1
  exact ay_conj_intro
    (AyGateFormula sub leftContext rightContext ->
      AyGateFormula aux2 leftContext rightContext)
    (AyGateFormula aux2 leftContext rightContext ->
      AyGateFormula sub leftContext rightContext)
    (ay_tseitin_gate_extension_sub_aux1_aux2
      sub aux1 aux2 leftContext rightContext
      aux1_equiv_sub aux2_equiv_aux1)
    (ay_tseitin_gate_projection_aux2_aux1_sub
      sub aux1 aux2 leftContext rightContext
      aux1_equiv_sub aux2_equiv_aux1)

theorem ay_tseitin_gate_extension_direction
    (sub : Prop) (aux1 : Prop) (aux2 : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux1 sub ->
    AyEquiv aux2 aux1 ->
    AyGateFormula sub leftContext rightContext ->
    AyGateFormula aux2 leftContext rightContext := by
  intro aux1_equiv_sub
  intro aux2_equiv_aux1
  exact ay_tseitin_gate_extension_sub_aux1_aux2
    sub aux1 aux2 leftContext rightContext
    aux1_equiv_sub aux2_equiv_aux1

theorem ay_tseitin_gate_projection_direction
    (sub : Prop) (aux1 : Prop) (aux2 : Prop)
    (leftContext : Prop) (rightContext : Prop) :
    AyEquiv aux1 sub ->
    AyEquiv aux2 aux1 ->
    AyGateFormula aux2 leftContext rightContext ->
    AyGateFormula sub leftContext rightContext := by
  intro aux1_equiv_sub
  intro aux2_equiv_aux1
  exact ay_tseitin_gate_projection_aux2_aux1_sub
    sub aux1 aux2 leftContext rightContext
    aux1_equiv_sub aux2_equiv_aux1
