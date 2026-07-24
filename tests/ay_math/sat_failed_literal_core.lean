-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for failed-literal probing.
-- A formula is satisfiable when some assignment satisfies it. A failed literal
-- proof says every model of the rest of the formula makes the literal false.

def AyFailedVar := Nat
def AyFailedAssignment := AyFailedVar -> Prop
def AyFailedFormula := AyFailedAssignment -> Prop
def AyFailedLiteral := AyFailedAssignment -> Prop

def AyFailedBoth (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedSatisfiable (formula : AyFailedFormula) : Prop :=
  forall result : Prop,
    ((assignment : AyFailedAssignment) -> formula assignment -> result) ->
    result

def AyFailedEquisat (left right : AyFailedFormula) : Prop :=
  AyFailedBoth
    (AyFailedSatisfiable left -> AyFailedSatisfiable right)
    (AyFailedSatisfiable right -> AyFailedSatisfiable left)

def AyFailedAssumeLiteral
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedFormula :=
  fun assignment => AyFailedBoth (formula assignment) (literal assignment)

def AyFailedAddNegatedLiteral
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedFormula :=
  fun assignment => AyFailedBoth (formula assignment) (Not (literal assignment))

def AyFailedLiteralProbe
    (formula : AyFailedFormula) (literal : AyFailedLiteral) : Prop :=
  forall assignment : AyFailedAssignment,
    formula assignment -> literal assignment -> False

def AyUnitPropagationPass
    (before : AyFailedFormula) (after : AyFailedFormula) : Prop :=
  AyFailedEquisat before after

theorem ay_failed_literal_derives_not
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    forall assignment : AyFailedAssignment,
      formula assignment -> Not (literal assignment) :=
  fun failed assignment formulaH literalH =>
    failed assignment formulaH literalH

theorem ay_failed_assumed_literal_unsat
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    Not (AyFailedSatisfiable (AyFailedAssumeLiteral formula literal)) :=
  fun failed assumedSat =>
    assumedSat False
      (fun assignment assumedH =>
        assumedH False
          (fun formulaH literalH =>
            failed assignment formulaH literalH))

theorem ay_failed_literal_add_not_forward
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyFailedSatisfiable formula ->
    AyFailedSatisfiable (AyFailedAddNegatedLiteral formula literal) :=
  fun failed formulaSat result keep =>
    formulaSat result
      (fun assignment formulaH =>
        keep assignment
          (fun pairResult pairKeep =>
            pairKeep formulaH
              (ay_failed_literal_derives_not formula literal
                failed assignment formulaH)))

theorem ay_failed_literal_add_not_backward
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedSatisfiable (AyFailedAddNegatedLiteral formula literal) ->
    AyFailedSatisfiable formula :=
  fun strengthenedSat result keep =>
    strengthenedSat result
      (fun assignment strengthenedH =>
        strengthenedH result
          (fun formulaH _notLiteralH =>
            keep assignment formulaH))

theorem ay_failed_literal_add_not_equisat
    (formula : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyFailedEquisat formula (AyFailedAddNegatedLiteral formula literal) :=
  fun failed result keep =>
    keep
      (ay_failed_literal_add_not_forward formula literal failed)
      (ay_failed_literal_add_not_backward formula literal)

theorem ay_failed_equisat_forward
    (before : AyFailedFormula) (after : AyFailedFormula) :
    AyFailedEquisat before after ->
    AyFailedSatisfiable before ->
    AyFailedSatisfiable after :=
  fun equisat =>
    equisat (AyFailedSatisfiable before -> AyFailedSatisfiable after)
      (fun forward _backward => forward)

theorem ay_failed_equisat_backward
    (before : AyFailedFormula) (after : AyFailedFormula) :
    AyFailedEquisat before after ->
    AyFailedSatisfiable after ->
    AyFailedSatisfiable before :=
  fun equisat =>
    equisat (AyFailedSatisfiable after -> AyFailedSatisfiable before)
      (fun _forward backward => backward)

theorem ay_failed_literal_then_unit_forward
    (formula propagated : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyUnitPropagationPass
      (AyFailedAddNegatedLiteral formula literal)
      propagated ->
    AyFailedSatisfiable formula ->
    AyFailedSatisfiable propagated :=
  fun failed unitPass formulaSat =>
    ay_failed_equisat_forward
      (AyFailedAddNegatedLiteral formula literal)
      propagated
      unitPass
      (ay_failed_literal_add_not_forward formula literal failed formulaSat)

theorem ay_failed_literal_then_unit_backward
    (formula propagated : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyUnitPropagationPass
      (AyFailedAddNegatedLiteral formula literal)
      propagated ->
    AyFailedSatisfiable propagated ->
    AyFailedSatisfiable formula :=
  fun _failed unitPass propagatedSat =>
    ay_failed_literal_add_not_backward formula literal
      (ay_failed_equisat_backward
        (AyFailedAddNegatedLiteral formula literal)
        propagated
        unitPass
        propagatedSat)

theorem ay_failed_literal_then_unit_equisat
    (formula propagated : AyFailedFormula) (literal : AyFailedLiteral) :
    AyFailedLiteralProbe formula literal ->
    AyUnitPropagationPass
      (AyFailedAddNegatedLiteral formula literal)
      propagated ->
    AyFailedEquisat formula propagated :=
  fun failed unitPass result keep =>
    keep
      (ay_failed_literal_then_unit_forward
        formula propagated literal failed unitPass)
      (ay_failed_literal_then_unit_backward
        formula propagated literal failed unitPass)
