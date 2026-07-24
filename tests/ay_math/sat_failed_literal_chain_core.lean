-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for failed-literal probing chains.
-- Each failed literal is represented as a proof that a model of the current
-- formula cannot make the probed literal true.

def AyFailedChainVar := Nat
def AyFailedChainAssignment := AyFailedChainVar -> Prop
def AyFailedChainFormula := AyFailedChainAssignment -> Prop
def AyFailedChainLiteral := AyFailedChainAssignment -> Prop

def AyFailedChainBoth (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedChainSatisfiable (formula : AyFailedChainFormula) : Prop :=
  forall result : Prop,
    ((assignment : AyFailedChainAssignment) -> formula assignment -> result) ->
    result

def AyFailedChainEquisat
    (left right : AyFailedChainFormula) : Prop :=
  AyFailedChainBoth
    (AyFailedChainSatisfiable left -> AyFailedChainSatisfiable right)
    (AyFailedChainSatisfiable right -> AyFailedChainSatisfiable left)

def AyFailedChainAddNegatedLiteral
    (formula : AyFailedChainFormula) (literal : AyFailedChainLiteral) :
    AyFailedChainFormula :=
  fun assignment =>
    AyFailedChainBoth (formula assignment) (Not (literal assignment))

def AyFailedChainProbe
    (formula : AyFailedChainFormula) (literal : AyFailedChainLiteral) :
    Prop :=
  forall assignment : AyFailedChainAssignment,
    formula assignment -> literal assignment -> False

def AyFailedChainUnitPropagationPass
    (before : AyFailedChainFormula) (after : AyFailedChainFormula) :
    Prop :=
  AyFailedChainEquisat before after

theorem ay_failed_chain_literal_derives_not
    (formula : AyFailedChainFormula) (literal : AyFailedChainLiteral) :
    AyFailedChainProbe formula literal ->
    forall assignment : AyFailedChainAssignment,
      formula assignment -> Not (literal assignment) :=
  fun failed assignment formulaH literalH =>
    failed assignment formulaH literalH

theorem ay_failed_chain_add_not_forward
    (formula : AyFailedChainFormula) (literal : AyFailedChainLiteral) :
    AyFailedChainProbe formula literal ->
    AyFailedChainSatisfiable formula ->
    AyFailedChainSatisfiable
      (AyFailedChainAddNegatedLiteral formula literal) :=
  fun failed formulaSat result keep =>
    formulaSat result
      (fun assignment formulaH =>
        keep assignment
          (fun pairResult pairKeep =>
            pairKeep formulaH
              (ay_failed_chain_literal_derives_not formula literal
                failed assignment formulaH)))

theorem ay_failed_chain_add_not_backward
    (formula : AyFailedChainFormula) (literal : AyFailedChainLiteral) :
    AyFailedChainSatisfiable
      (AyFailedChainAddNegatedLiteral formula literal) ->
    AyFailedChainSatisfiable formula :=
  fun strengthenedSat result keep =>
    strengthenedSat result
      (fun assignment strengthenedH =>
        strengthenedH result
          (fun formulaH _notLiteralH =>
            keep assignment formulaH))

theorem ay_failed_chain_add_not_equisat
    (formula : AyFailedChainFormula) (literal : AyFailedChainLiteral) :
    AyFailedChainProbe formula literal ->
    AyFailedChainEquisat
      formula
      (AyFailedChainAddNegatedLiteral formula literal) :=
  fun failed result keep =>
    keep
      (ay_failed_chain_add_not_forward formula literal failed)
      (ay_failed_chain_add_not_backward formula literal)

theorem ay_failed_chain_equisat_forward
    (before : AyFailedChainFormula) (after : AyFailedChainFormula) :
    AyFailedChainEquisat before after ->
    AyFailedChainSatisfiable before ->
    AyFailedChainSatisfiable after :=
  fun equisat =>
    equisat
      (AyFailedChainSatisfiable before ->
        AyFailedChainSatisfiable after)
      (fun forward _backward => forward)

theorem ay_failed_chain_equisat_backward
    (before : AyFailedChainFormula) (after : AyFailedChainFormula) :
    AyFailedChainEquisat before after ->
    AyFailedChainSatisfiable after ->
    AyFailedChainSatisfiable before :=
  fun equisat =>
    equisat
      (AyFailedChainSatisfiable after ->
        AyFailedChainSatisfiable before)
      (fun _forward backward => backward)

theorem ay_failed_chain_two_additions_forward
    (formula : AyFailedChainFormula)
    (firstLiteral secondLiteral : AyFailedChainLiteral) :
    AyFailedChainProbe formula firstLiteral ->
    AyFailedChainProbe
      (AyFailedChainAddNegatedLiteral formula firstLiteral)
      secondLiteral ->
    AyFailedChainSatisfiable formula ->
    AyFailedChainSatisfiable
      (AyFailedChainAddNegatedLiteral
        (AyFailedChainAddNegatedLiteral formula firstLiteral)
        secondLiteral) :=
  fun firstFailed secondFailed formulaSat =>
    ay_failed_chain_add_not_forward
      (AyFailedChainAddNegatedLiteral formula firstLiteral)
      secondLiteral
      secondFailed
      (ay_failed_chain_add_not_forward
        formula
        firstLiteral
        firstFailed
        formulaSat)

theorem ay_failed_chain_two_additions_backward
    (formula : AyFailedChainFormula)
    (firstLiteral secondLiteral : AyFailedChainLiteral) :
    AyFailedChainSatisfiable
      (AyFailedChainAddNegatedLiteral
        (AyFailedChainAddNegatedLiteral formula firstLiteral)
        secondLiteral) ->
    AyFailedChainSatisfiable formula :=
  fun chainSat =>
    ay_failed_chain_add_not_backward formula firstLiteral
      (ay_failed_chain_add_not_backward
        (AyFailedChainAddNegatedLiteral formula firstLiteral)
        secondLiteral
        chainSat)

theorem ay_failed_chain_two_additions_equisat
    (formula : AyFailedChainFormula)
    (firstLiteral secondLiteral : AyFailedChainLiteral) :
    AyFailedChainProbe formula firstLiteral ->
    AyFailedChainProbe
      (AyFailedChainAddNegatedLiteral formula firstLiteral)
      secondLiteral ->
    AyFailedChainEquisat
      formula
      (AyFailedChainAddNegatedLiteral
        (AyFailedChainAddNegatedLiteral formula firstLiteral)
        secondLiteral) :=
  fun firstFailed secondFailed result keep =>
    keep
      (ay_failed_chain_two_additions_forward
        formula firstLiteral secondLiteral firstFailed secondFailed)
      (ay_failed_chain_two_additions_backward
        formula firstLiteral secondLiteral)

theorem ay_failed_chain_add_then_unit_forward
    (formula propagated : AyFailedChainFormula)
    (literal : AyFailedChainLiteral) :
    AyFailedChainProbe formula literal ->
    AyFailedChainUnitPropagationPass
      (AyFailedChainAddNegatedLiteral formula literal)
      propagated ->
    AyFailedChainSatisfiable formula ->
    AyFailedChainSatisfiable propagated :=
  fun failed unitPass formulaSat =>
    ay_failed_chain_equisat_forward
      (AyFailedChainAddNegatedLiteral formula literal)
      propagated
      unitPass
      (ay_failed_chain_add_not_forward
        formula literal failed formulaSat)

theorem ay_failed_chain_add_then_unit_backward
    (formula propagated : AyFailedChainFormula)
    (literal : AyFailedChainLiteral) :
    AyFailedChainProbe formula literal ->
    AyFailedChainUnitPropagationPass
      (AyFailedChainAddNegatedLiteral formula literal)
      propagated ->
    AyFailedChainSatisfiable propagated ->
    AyFailedChainSatisfiable formula :=
  fun _failed unitPass propagatedSat =>
    ay_failed_chain_add_not_backward formula literal
      (ay_failed_chain_equisat_backward
        (AyFailedChainAddNegatedLiteral formula literal)
        propagated
        unitPass
        propagatedSat)

theorem ay_failed_chain_add_then_unit_equisat
    (formula propagated : AyFailedChainFormula)
    (literal : AyFailedChainLiteral) :
    AyFailedChainProbe formula literal ->
    AyFailedChainUnitPropagationPass
      (AyFailedChainAddNegatedLiteral formula literal)
      propagated ->
    AyFailedChainEquisat formula propagated :=
  fun failed unitPass result keep =>
    keep
      (ay_failed_chain_add_then_unit_forward
        formula propagated literal failed unitPass)
      (ay_failed_chain_add_then_unit_backward
        formula propagated literal failed unitPass)
