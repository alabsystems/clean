-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for failed-literal probing interacting with
-- hyper-binary resolution. A failed probe yields a unit Not l; an HBR witness
-- can use that unit to derive an additional implied clause/literal.

def AyFailedHbrVar := Nat
def AyFailedHbrAssignment := AyFailedHbrVar -> Prop
def AyFailedHbrFormula := AyFailedHbrAssignment -> Prop
def AyFailedHbrLiteral := AyFailedHbrAssignment -> Prop
def AyFailedHbrClause := AyFailedHbrAssignment -> Prop

def AyFailedHbrBoth (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedHbrSatisfiable (formula : AyFailedHbrFormula) : Prop :=
  forall result : Prop,
    ((assignment : AyFailedHbrAssignment) -> formula assignment -> result) ->
    result

def AyFailedHbrEquisat
    (left right : AyFailedHbrFormula) : Prop :=
  AyFailedHbrBoth
    (AyFailedHbrSatisfiable left -> AyFailedHbrSatisfiable right)
    (AyFailedHbrSatisfiable right -> AyFailedHbrSatisfiable left)

def AyFailedHbrAddNegatedLiteral
    (formula : AyFailedHbrFormula) (literal : AyFailedHbrLiteral) :
    AyFailedHbrFormula :=
  fun assignment =>
    AyFailedHbrBoth (formula assignment) (Not (literal assignment))

def AyFailedHbrAddClause
    (formula : AyFailedHbrFormula) (clause : AyFailedHbrClause) :
    AyFailedHbrFormula :=
  fun assignment =>
    AyFailedHbrBoth (formula assignment) (clause assignment)

def AyFailedHbrAddFailedThenClause
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (clause : AyFailedHbrClause) :
    AyFailedHbrFormula :=
  AyFailedHbrAddClause
    (AyFailedHbrAddNegatedLiteral formula literal)
    clause

def AyFailedHbrProbe
    (formula : AyFailedHbrFormula) (literal : AyFailedHbrLiteral) :
    Prop :=
  forall assignment : AyFailedHbrAssignment,
    formula assignment -> literal assignment -> False

def AyFailedHbrWitness
    (formula : AyFailedHbrFormula)
    (unitLiteral : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    Prop :=
  forall assignment : AyFailedHbrAssignment,
    formula assignment -> Not (unitLiteral assignment) -> derived assignment

theorem ay_failed_hbr_failed_unit
    (formula : AyFailedHbrFormula) (literal : AyFailedHbrLiteral) :
    AyFailedHbrProbe formula literal ->
    forall assignment : AyFailedHbrAssignment,
      formula assignment -> Not (literal assignment) :=
  fun failed assignment formulaH literalH =>
    failed assignment formulaH literalH

theorem ay_failed_hbr_unit_feeds_witness
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrProbe formula literal ->
    AyFailedHbrWitness formula literal derived ->
    forall assignment : AyFailedHbrAssignment,
      formula assignment -> derived assignment :=
  fun failed witness assignment formulaH =>
    witness assignment formulaH
      (ay_failed_hbr_failed_unit formula literal
        failed assignment formulaH)

theorem ay_failed_hbr_add_failed_forward
    (formula : AyFailedHbrFormula) (literal : AyFailedHbrLiteral) :
    AyFailedHbrProbe formula literal ->
    AyFailedHbrSatisfiable formula ->
    AyFailedHbrSatisfiable
      (AyFailedHbrAddNegatedLiteral formula literal) :=
  fun failed formulaSat result keep =>
    formulaSat result
      (fun assignment formulaH =>
        keep assignment
          (fun pairResult pairKeep =>
            pairKeep formulaH
              (ay_failed_hbr_failed_unit formula literal
                failed assignment formulaH)))

theorem ay_failed_hbr_add_failed_backward
    (formula : AyFailedHbrFormula) (literal : AyFailedHbrLiteral) :
    AyFailedHbrSatisfiable
      (AyFailedHbrAddNegatedLiteral formula literal) ->
    AyFailedHbrSatisfiable formula :=
  fun strengthenedSat result keep =>
    strengthenedSat result
      (fun assignment strengthenedH =>
        strengthenedH result
          (fun formulaH _unitH =>
            keep assignment formulaH))

theorem ay_failed_hbr_add_failed_equisat
    (formula : AyFailedHbrFormula) (literal : AyFailedHbrLiteral) :
    AyFailedHbrProbe formula literal ->
    AyFailedHbrEquisat
      formula
      (AyFailedHbrAddNegatedLiteral formula literal) :=
  fun failed result keep =>
    keep
      (ay_failed_hbr_add_failed_forward formula literal failed)
      (ay_failed_hbr_add_failed_backward formula literal)

theorem ay_failed_hbr_add_derived_forward
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrWitness formula literal derived ->
    AyFailedHbrSatisfiable
      (AyFailedHbrAddNegatedLiteral formula literal) ->
    AyFailedHbrSatisfiable
      (AyFailedHbrAddFailedThenClause formula literal derived) :=
  fun witness unitSat result keep =>
    unitSat result
      (fun assignment unitH =>
        unitH result
          (fun formulaH notLiteralH =>
            keep assignment
              (fun pairResult pairKeep =>
                pairKeep unitH
                  (witness assignment formulaH notLiteralH))))

theorem ay_failed_hbr_add_derived_backward
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrSatisfiable
      (AyFailedHbrAddFailedThenClause formula literal derived) ->
    AyFailedHbrSatisfiable
      (AyFailedHbrAddNegatedLiteral formula literal) :=
  fun withDerivedSat result keep =>
    withDerivedSat result
      (fun assignment withDerivedH =>
        withDerivedH result
          (fun unitH _derivedH =>
            keep assignment unitH))

theorem ay_failed_hbr_add_derived_equisat
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrWitness formula literal derived ->
    AyFailedHbrEquisat
      (AyFailedHbrAddNegatedLiteral formula literal)
      (AyFailedHbrAddFailedThenClause formula literal derived) :=
  fun witness result keep =>
    keep
      (ay_failed_hbr_add_derived_forward formula literal derived witness)
      (ay_failed_hbr_add_derived_backward formula literal derived)

theorem ay_failed_hbr_composed_forward
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrProbe formula literal ->
    AyFailedHbrWitness formula literal derived ->
    AyFailedHbrSatisfiable formula ->
    AyFailedHbrSatisfiable
      (AyFailedHbrAddFailedThenClause formula literal derived) :=
  fun failed witness formulaSat =>
    ay_failed_hbr_add_derived_forward formula literal derived witness
      (ay_failed_hbr_add_failed_forward formula literal failed formulaSat)

theorem ay_failed_hbr_composed_backward
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrSatisfiable
      (AyFailedHbrAddFailedThenClause formula literal derived) ->
    AyFailedHbrSatisfiable formula :=
  fun composedSat =>
    ay_failed_hbr_add_failed_backward formula literal
      (ay_failed_hbr_add_derived_backward
        formula literal derived composedSat)

theorem ay_failed_hbr_composed_equisat
    (formula : AyFailedHbrFormula)
    (literal : AyFailedHbrLiteral)
    (derived : AyFailedHbrClause) :
    AyFailedHbrProbe formula literal ->
    AyFailedHbrWitness formula literal derived ->
    AyFailedHbrEquisat
      formula
      (AyFailedHbrAddFailedThenClause formula literal derived) :=
  fun failed witness result keep =>
    keep
      (ay_failed_hbr_composed_forward
        formula literal derived failed witness)
      (ay_failed_hbr_composed_backward
        formula literal derived)
