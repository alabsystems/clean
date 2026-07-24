-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for SCC/equivalence substitution interacting with
-- failed-literal probing. The package is self-contained and uses Church
-- encodings, matching the SAT-COMP-facing theorem style.

def AyFailedVar := Nat
def AyFailedAssignment := AyFailedVar -> Prop
def AyFailedFormula := AyFailedAssignment -> Prop
def AyFailedLiteral := AyFailedAssignment -> Prop

def AyBoth (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedSatisfiable (formula : AyFailedFormula) : Prop :=
  forall result : Prop,
    ((assignment : AyFailedAssignment) -> formula assignment -> result) ->
    result

def AyFailedEquisat (left right : AyFailedFormula) : Prop :=
  AyBoth
    (AyFailedSatisfiable left -> AyFailedSatisfiable right)
    (AyFailedSatisfiable right -> AyFailedSatisfiable left)

def AyFailedAddNegatedLiteral
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedFormula :=
  fun assignment => AyBoth (formula assignment) (Not (literal assignment))

def AyFailedLiteralProbe
    (formula : AyFailedFormula) (literal : AyFailedLiteral) : Prop :=
  forall assignment : AyFailedAssignment,
    formula assignment -> literal assignment -> False

def AyLiteralEquiv
    (left right : AyFailedLiteral) : Prop :=
  forall assignment : AyFailedAssignment,
    AyBoth
      (left assignment -> right assignment)
      (right assignment -> left assignment)

theorem ay_both_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBoth left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_literal_equiv_forward
    (left right : AyFailedLiteral) :
    AyLiteralEquiv left right ->
    forall assignment : AyFailedAssignment,
      left assignment -> right assignment := by
  intro equiv
  intro assignment
  exact equiv assignment
    (left assignment -> right assignment)
    (fun forward _backward => forward)

theorem ay_literal_equiv_backward
    (left right : AyFailedLiteral) :
    AyLiteralEquiv left right ->
    forall assignment : AyFailedAssignment,
      right assignment -> left assignment := by
  intro equiv
  intro assignment
  exact equiv assignment
    (right assignment -> left assignment)
    (fun _forward backward => backward)

theorem ay_failed_probe_equiv_forward
    (formula : AyFailedFormula)
    (literal equivLiteral : AyFailedLiteral) :
    AyLiteralEquiv literal equivLiteral ->
    AyFailedLiteralProbe formula literal ->
    AyFailedLiteralProbe formula equivLiteral := by
  intro literal_equiv
  intro failed
  intro assignment
  intro formulaH
  intro equivLiteralH
  exact failed assignment formulaH
    (ay_literal_equiv_backward literal equivLiteral
      literal_equiv assignment equivLiteralH)

theorem ay_failed_probe_equiv_backward
    (formula : AyFailedFormula)
    (literal equivLiteral : AyFailedLiteral) :
    AyLiteralEquiv literal equivLiteral ->
    AyFailedLiteralProbe formula equivLiteral ->
    AyFailedLiteralProbe formula literal := by
  intro literal_equiv
  intro failed
  intro assignment
  intro formulaH
  intro literalH
  exact failed assignment formulaH
    (ay_literal_equiv_forward literal equivLiteral
      literal_equiv assignment literalH)

theorem ay_failed_literal_derives_not
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    forall assignment : AyFailedAssignment,
      formula assignment -> Not (literal assignment) := by
  intro failed
  intro assignment
  intro formulaH
  intro literalH
  exact failed assignment formulaH literalH

theorem ay_failed_literal_add_not_forward
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyFailedSatisfiable formula ->
    AyFailedSatisfiable (AyFailedAddNegatedLiteral formula literal) := by
  intro failed
  intro formulaSat
  intro result
  intro keep
  exact formulaSat result
    (fun assignment formulaH =>
      keep assignment
        (ay_both_intro
          (formula assignment)
          (Not (literal assignment))
          formulaH
          (ay_failed_literal_derives_not formula literal
            failed assignment formulaH)))

theorem ay_failed_literal_add_not_backward
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedSatisfiable (AyFailedAddNegatedLiteral formula literal) ->
    AyFailedSatisfiable formula := by
  intro strengthenedSat
  intro result
  intro keep
  exact strengthenedSat result
    (fun assignment strengthenedH =>
      strengthenedH result
        (fun formulaH _notLiteralH =>
          keep assignment formulaH))

theorem ay_failed_literal_add_not_equisat
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyFailedEquisat formula (AyFailedAddNegatedLiteral formula literal) := by
  intro failed
  exact ay_both_intro
    (AyFailedSatisfiable formula ->
      AyFailedSatisfiable (AyFailedAddNegatedLiteral formula literal))
    (AyFailedSatisfiable (AyFailedAddNegatedLiteral formula literal) ->
      AyFailedSatisfiable formula)
    (ay_failed_literal_add_not_forward formula literal failed)
    (ay_failed_literal_add_not_backward formula literal)

theorem ay_equiv_failed_literal_add_not_forward
    (formula : AyFailedFormula)
    (literal equivLiteral : AyFailedLiteral) :
    AyLiteralEquiv literal equivLiteral ->
    AyFailedLiteralProbe formula literal ->
    AyFailedSatisfiable formula ->
    AyFailedSatisfiable
      (AyFailedAddNegatedLiteral formula equivLiteral) := by
  intro literal_equiv
  intro failed
  exact ay_failed_literal_add_not_forward formula equivLiteral
    (ay_failed_probe_equiv_forward
      formula literal equivLiteral literal_equiv failed)

theorem ay_equiv_failed_literal_add_not_backward
    (formula : AyFailedFormula)
    (literal equivLiteral : AyFailedLiteral) :
    AyFailedSatisfiable
      (AyFailedAddNegatedLiteral formula equivLiteral) ->
    AyFailedSatisfiable formula := by
  intro strengthenedSat
  exact ay_failed_literal_add_not_backward
    formula equivLiteral strengthenedSat

theorem ay_equiv_failed_literal_add_not_equisat
    (formula : AyFailedFormula)
    (literal equivLiteral : AyFailedLiteral) :
    AyLiteralEquiv literal equivLiteral ->
    AyFailedLiteralProbe formula literal ->
    AyFailedEquisat
      formula
      (AyFailedAddNegatedLiteral formula equivLiteral) := by
  intro literal_equiv
  intro failed
  exact ay_both_intro
    (AyFailedSatisfiable formula ->
      AyFailedSatisfiable
        (AyFailedAddNegatedLiteral formula equivLiteral))
    (AyFailedSatisfiable
      (AyFailedAddNegatedLiteral formula equivLiteral) ->
        AyFailedSatisfiable formula)
    (ay_equiv_failed_literal_add_not_forward
      formula literal equivLiteral literal_equiv failed)
    (ay_equiv_failed_literal_add_not_backward
      formula literal equivLiteral)

theorem ay_equiv_failed_probe_and_unit_pair
    (formula : AyFailedFormula)
    (literal equivLiteral : AyFailedLiteral) :
    AyLiteralEquiv literal equivLiteral ->
    AyFailedLiteralProbe formula literal ->
    AyBoth
      (AyFailedLiteralProbe formula equivLiteral)
      (AyFailedEquisat
        formula
        (AyFailedAddNegatedLiteral formula equivLiteral)) := by
  intro literal_equiv
  intro failed
  exact ay_both_intro
    (AyFailedLiteralProbe formula equivLiteral)
    (AyFailedEquisat
      formula
      (AyFailedAddNegatedLiteral formula equivLiteral))
    (ay_failed_probe_equiv_forward
      formula literal equivLiteral literal_equiv failed)
    (ay_equiv_failed_literal_add_not_equisat
      formula literal equivLiteral literal_equiv failed)
