-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained backbone detection kernels. Failed-literal probing is modeled
-- as a certificate that every model of the formula forces the backbone literal.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyFormulaWithUnit (formula : Prop) (unitLit : Prop) :=
  AyConj formula unitLit

def AyFailedOppositeProbe (formula : Prop) (unitLit : Prop) :=
  formula -> unitLit

def AyBackboneLiteral (formula : Prop) (unitLit : Prop) :=
  formula -> unitLit

def AyLiteralEquiv (leftLit : Prop) (rightLit : Prop) :=
  AyConj (leftLit -> rightLit) (rightLit -> leftLit)

def AyVivificationOriginal (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyConj (AyDisj lit shorter) rest

def AyVivificationPruned (shorter : Prop) (rest : Prop) :=
  AyConj shorter rest

def AyVivificationSideCondition (lit : Prop) (shorter : Prop) (rest : Prop) :=
  lit -> rest -> shorter

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
  intro pair
  exact pair p
    (fun hp _hq => hp)

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyEquisat original transformed := by
  intro forward
  intro backward
  exact ay_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_equisat_forward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    original -> transformed := by
  intro equisat
  exact equisat (original -> transformed)
    (fun forward _backward => forward)

theorem ay_equisat_backward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    transformed -> original := by
  intro equisat
  exact equisat (transformed -> original)
    (fun _forward backward => backward)

theorem ay_equisat_trans
    (a : Prop) (b : Prop) (c : Prop) :
    AyEquisat a b ->
    AyEquisat b c ->
    AyEquisat a c := by
  intro ab
  intro bc
  exact ay_equisat_intro a c
    (fun ha =>
      ay_equisat_forward b c bc
        (ay_equisat_forward a b ab ha))
    (fun hc =>
      ay_equisat_backward a b ab
        (ay_equisat_backward b c bc hc))

theorem ay_formula_with_unit_project_formula
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    formula := by
  intro withUnit
  exact withUnit formula
    (fun hformula _hunit => hformula)

theorem ay_formula_with_unit_project_unit
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    unitLit := by
  intro withUnit
  exact withUnit unitLit
    (fun _hformula hunit => hunit)

theorem ay_failed_probe_forces_backbone
    (formula : Prop) (unitLit : Prop) :
    AyFailedOppositeProbe formula unitLit ->
    AyBackboneLiteral formula unitLit := by
  intro failedOpposite
  intro hformula
  exact failedOpposite hformula

theorem ay_backbone_unit_add_forward
    (formula : Prop) (unitLit : Prop) :
    AyBackboneLiteral formula unitLit ->
    formula ->
    AyFormulaWithUnit formula unitLit := by
  intro backbone
  intro hformula
  exact ay_conj_intro formula unitLit
    hformula
    (backbone hformula)

theorem ay_backbone_unit_add_backward
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    formula := by
  intro withUnit
  exact ay_formula_with_unit_project_formula formula unitLit withUnit

theorem ay_backbone_unit_add_equisat
    (formula : Prop) (unitLit : Prop) :
    AyBackboneLiteral formula unitLit ->
    AyEquisat formula (AyFormulaWithUnit formula unitLit) := by
  intro backbone
  exact ay_equisat_intro
    formula
    (AyFormulaWithUnit formula unitLit)
    (ay_backbone_unit_add_forward formula unitLit backbone)
    (ay_backbone_unit_add_backward formula unitLit)

theorem ay_failed_probe_adds_backbone_unit_equisat
    (formula : Prop) (unitLit : Prop) :
    AyFailedOppositeProbe formula unitLit ->
    AyEquisat formula (AyFormulaWithUnit formula unitLit) := by
  intro failedOpposite
  exact ay_backbone_unit_add_equisat formula unitLit
    (ay_failed_probe_forces_backbone formula unitLit failedOpposite)

theorem ay_literal_equiv_forward
    (leftLit : Prop) (rightLit : Prop) :
    AyLiteralEquiv leftLit rightLit ->
    leftLit -> rightLit := by
  intro litEquiv
  exact litEquiv (leftLit -> rightLit)
    (fun forward _backward => forward)

theorem ay_literal_equiv_backward
    (leftLit : Prop) (rightLit : Prop) :
    AyLiteralEquiv leftLit rightLit ->
    rightLit -> leftLit := by
  intro litEquiv
  exact litEquiv (rightLit -> leftLit)
    (fun _forward backward => backward)

theorem ay_backbone_substitute_equivalent_literal
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyLiteralEquiv oldLit newLit ->
    AyBackboneLiteral formula oldLit ->
    AyBackboneLiteral formula newLit := by
  intro litEquiv
  intro oldBackbone
  intro hformula
  exact ay_literal_equiv_forward oldLit newLit litEquiv
    (oldBackbone hformula)

theorem ay_formula_with_unit_equiv_substitution_forward
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyLiteralEquiv oldLit newLit ->
    AyFormulaWithUnit formula oldLit ->
    AyFormulaWithUnit formula newLit := by
  intro litEquiv
  intro oldUnit
  exact ay_conj_intro formula newLit
    (ay_formula_with_unit_project_formula formula oldLit oldUnit)
    (ay_literal_equiv_forward oldLit newLit litEquiv
      (ay_formula_with_unit_project_unit formula oldLit oldUnit))

theorem ay_formula_with_unit_equiv_substitution_backward
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyLiteralEquiv oldLit newLit ->
    AyFormulaWithUnit formula newLit ->
    AyFormulaWithUnit formula oldLit := by
  intro litEquiv
  intro newUnit
  exact ay_conj_intro formula oldLit
    (ay_formula_with_unit_project_formula formula newLit newUnit)
    (ay_literal_equiv_backward oldLit newLit litEquiv
      (ay_formula_with_unit_project_unit formula newLit newUnit))

theorem ay_backbone_unit_equiv_substitution_equisat
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyLiteralEquiv oldLit newLit ->
    AyEquisat
      (AyFormulaWithUnit formula oldLit)
      (AyFormulaWithUnit formula newLit) := by
  intro litEquiv
  exact ay_equisat_intro
    (AyFormulaWithUnit formula oldLit)
    (AyFormulaWithUnit formula newLit)
    (ay_formula_with_unit_equiv_substitution_forward
      formula oldLit newLit litEquiv)
    (ay_formula_with_unit_equiv_substitution_backward
      formula oldLit newLit litEquiv)

theorem ay_backbone_equiv_substitution_composed_equisat
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyBackboneLiteral formula oldLit ->
    AyLiteralEquiv oldLit newLit ->
    AyEquisat formula (AyFormulaWithUnit formula newLit) := by
  intro oldBackbone
  intro litEquiv
  exact ay_equisat_trans
    formula
    (AyFormulaWithUnit formula oldLit)
    (AyFormulaWithUnit formula newLit)
    (ay_backbone_unit_add_equisat formula oldLit oldBackbone)
    (ay_backbone_unit_equiv_substitution_equisat
      formula oldLit newLit litEquiv)

theorem ay_vivification_forward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyVivificationOriginal lit shorter rest ->
    AyVivificationPruned shorter rest := by
  intro side
  intro original
  intro result
  intro build
  exact original result
    (fun clause hrest =>
      clause result
        (fun hlit => build (side hlit hrest) hrest)
        (fun hshorter => build hshorter hrest))

theorem ay_vivification_backward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationPruned shorter rest ->
    AyVivificationOriginal lit shorter rest := by
  intro pruned
  intro result
  intro build
  exact pruned result
    (fun hshorter hrest =>
      build
        (ay_disj_right lit shorter hshorter)
        hrest)

theorem ay_vivification_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyVivificationPruned shorter rest) := by
  intro side
  exact ay_equisat_intro
    (AyVivificationOriginal lit shorter rest)
    (AyVivificationPruned shorter rest)
    (ay_vivification_forward lit shorter rest side)
    (ay_vivification_backward lit shorter rest)

theorem ay_backbone_transport_through_equisat_forward
    (before : Prop) (after : Prop) (unitLit : Prop) :
    AyEquisat before after ->
    AyBackboneLiteral after unitLit ->
    AyBackboneLiteral before unitLit := by
  intro equisat
  intro afterBackbone
  intro hbefore
  exact afterBackbone
    (ay_equisat_forward before after equisat hbefore)

theorem ay_backbone_transport_through_equisat_backward
    (before : Prop) (after : Prop) (unitLit : Prop) :
    AyEquisat before after ->
    AyBackboneLiteral before unitLit ->
    AyBackboneLiteral after unitLit := by
  intro equisat
  intro beforeBackbone
  intro hafter
  exact beforeBackbone
    (ay_equisat_backward before after equisat hafter)

theorem ay_backbone_unit_after_vivification_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) (unitLit : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyBackboneLiteral (AyVivificationPruned shorter rest) unitLit ->
    AyEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyFormulaWithUnit
        (AyVivificationPruned shorter rest)
        unitLit) := by
  intro side
  intro backbone
  exact ay_equisat_trans
    (AyVivificationOriginal lit shorter rest)
    (AyVivificationPruned shorter rest)
    (AyFormulaWithUnit
      (AyVivificationPruned shorter rest)
      unitLit)
    (ay_vivification_equisat lit shorter rest side)
    (ay_backbone_unit_add_equisat
      (AyVivificationPruned shorter rest)
      unitLit
      backbone)

theorem ay_failed_probe_vivification_composed_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) (unitLit : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyFailedOppositeProbe
      (AyVivificationPruned shorter rest)
      unitLit ->
    AyEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyFormulaWithUnit
        (AyVivificationPruned shorter rest)
        unitLit) := by
  intro side
  intro failedOpposite
  exact ay_backbone_unit_after_vivification_equisat
    lit shorter rest unitLit
    side
    (ay_failed_probe_forces_backbone
      (AyVivificationPruned shorter rest)
      unitLit
      failedOpposite)
