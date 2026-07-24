-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for failed-literal probing interacting with
-- clause vivification. A failed probe derives a unit Not l; a vivification
-- witness may use that unit to justify replacing an old clause by a stronger
-- vivified clause.

def AyFailedVivVar := Nat
def AyFailedVivAssignment := AyFailedVivVar -> Prop
def AyFailedVivFormula := AyFailedVivAssignment -> Prop
def AyFailedVivLiteral := AyFailedVivAssignment -> Prop
def AyFailedVivClause := AyFailedVivAssignment -> Prop

def AyFailedVivBoth (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedVivSatisfiable (formula : AyFailedVivFormula) : Prop :=
  forall result : Prop,
    ((assignment : AyFailedVivAssignment) -> formula assignment -> result) ->
    result

def AyFailedVivEquisat
    (left right : AyFailedVivFormula) : Prop :=
  AyFailedVivBoth
    (AyFailedVivSatisfiable left -> AyFailedVivSatisfiable right)
    (AyFailedVivSatisfiable right -> AyFailedVivSatisfiable left)

def AyFailedVivWithClause
    (rest : AyFailedVivFormula) (clause : AyFailedVivClause) :
    AyFailedVivFormula :=
  fun assignment => AyFailedVivBoth (rest assignment) (clause assignment)

def AyFailedVivAddUnit
    (rest : AyFailedVivFormula) (literal : AyFailedVivLiteral) :
    AyFailedVivFormula :=
  fun assignment => AyFailedVivBoth (rest assignment) (Not (literal assignment))

def AyFailedVivProbe
    (rest : AyFailedVivFormula) (literal : AyFailedVivLiteral) :
    Prop :=
  forall assignment : AyFailedVivAssignment,
    rest assignment -> literal assignment -> False

def AyFailedVivSideWitness
    (rest : AyFailedVivFormula)
    (literal : AyFailedVivLiteral)
    (oldClause vivifiedClause : AyFailedVivClause) :
    Prop :=
  forall assignment : AyFailedVivAssignment,
    rest assignment ->
    Not (literal assignment) ->
    oldClause assignment ->
    vivifiedClause assignment

def AyFailedVivStrengtheningWitness
    (oldClause vivifiedClause : AyFailedVivClause) :
    Prop :=
  forall assignment : AyFailedVivAssignment,
    vivifiedClause assignment -> oldClause assignment

theorem ay_failed_viv_failed_unit
    (rest : AyFailedVivFormula) (literal : AyFailedVivLiteral) :
    AyFailedVivProbe rest literal ->
    forall assignment : AyFailedVivAssignment,
      rest assignment -> Not (literal assignment) :=
  fun failed assignment restH literalH =>
    failed assignment restH literalH

theorem ay_failed_viv_add_unit_forward
    (rest : AyFailedVivFormula) (literal : AyFailedVivLiteral) :
    AyFailedVivProbe rest literal ->
    AyFailedVivSatisfiable rest ->
    AyFailedVivSatisfiable (AyFailedVivAddUnit rest literal) :=
  fun failed restSat result keep =>
    restSat result
      (fun assignment restH =>
        keep assignment
          (fun pairResult pairKeep =>
            pairKeep restH
              (ay_failed_viv_failed_unit rest literal
                failed assignment restH)))

theorem ay_failed_viv_add_unit_backward
    (rest : AyFailedVivFormula) (literal : AyFailedVivLiteral) :
    AyFailedVivSatisfiable (AyFailedVivAddUnit rest literal) ->
    AyFailedVivSatisfiable rest :=
  fun unitSat result keep =>
    unitSat result
      (fun assignment unitH =>
        unitH result
          (fun restH _notLiteralH =>
            keep assignment restH))

theorem ay_failed_viv_add_unit_equisat
    (rest : AyFailedVivFormula) (literal : AyFailedVivLiteral) :
    AyFailedVivProbe rest literal ->
    AyFailedVivEquisat rest (AyFailedVivAddUnit rest literal) :=
  fun failed result keep =>
    keep
      (ay_failed_viv_add_unit_forward rest literal failed)
      (ay_failed_viv_add_unit_backward rest literal)

theorem ay_failed_viv_side_condition_available
    (rest : AyFailedVivFormula)
    (literal : AyFailedVivLiteral)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivProbe rest literal ->
    AyFailedVivSideWitness rest literal oldClause vivifiedClause ->
    forall assignment : AyFailedVivAssignment,
      rest assignment ->
      oldClause assignment ->
      vivifiedClause assignment :=
  fun failed side assignment restH oldH =>
    side assignment restH
      (ay_failed_viv_failed_unit rest literal failed assignment restH)
      oldH

theorem ay_failed_viv_replace_forward
    (rest : AyFailedVivFormula)
    (literal : AyFailedVivLiteral)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivProbe rest literal ->
    AyFailedVivSideWitness rest literal oldClause vivifiedClause ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest oldClause) ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest vivifiedClause) :=
  fun failed side originalSat result keep =>
    originalSat result
      (fun assignment originalH =>
        originalH result
          (fun restH oldH =>
            keep assignment
              (fun pairResult pairKeep =>
                pairKeep restH
                  (side assignment restH
                    (ay_failed_viv_failed_unit rest literal
                      failed assignment restH)
                    oldH))))

theorem ay_failed_viv_replace_backward
    (rest : AyFailedVivFormula)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivStrengtheningWitness oldClause vivifiedClause ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest vivifiedClause) ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest oldClause) :=
  fun strengthens vivifiedSat result keep =>
    vivifiedSat result
      (fun assignment vivifiedH =>
        vivifiedH result
          (fun restH vivifiedClauseH =>
            keep assignment
              (fun pairResult pairKeep =>
                pairKeep restH
                  (strengthens assignment vivifiedClauseH))))

theorem ay_failed_viv_replace_equisat
    (rest : AyFailedVivFormula)
    (literal : AyFailedVivLiteral)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivProbe rest literal ->
    AyFailedVivSideWitness rest literal oldClause vivifiedClause ->
    AyFailedVivStrengtheningWitness oldClause vivifiedClause ->
    AyFailedVivEquisat
      (AyFailedVivWithClause rest oldClause)
      (AyFailedVivWithClause rest vivifiedClause) :=
  fun failed side strengthens result keep =>
    keep
      (ay_failed_viv_replace_forward
        rest literal oldClause vivifiedClause failed side)
      (ay_failed_viv_replace_backward
        rest oldClause vivifiedClause strengthens)

theorem ay_failed_viv_composed_forward
    (rest : AyFailedVivFormula)
    (literal : AyFailedVivLiteral)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivProbe rest literal ->
    AyFailedVivSideWitness rest literal oldClause vivifiedClause ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest oldClause) ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest vivifiedClause) :=
  fun failed side originalSat =>
    ay_failed_viv_replace_forward
      rest literal oldClause vivifiedClause failed side originalSat

theorem ay_failed_viv_composed_backward
    (rest : AyFailedVivFormula)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivStrengtheningWitness oldClause vivifiedClause ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest vivifiedClause) ->
    AyFailedVivSatisfiable (AyFailedVivWithClause rest oldClause) :=
  fun strengthens vivifiedSat =>
    ay_failed_viv_replace_backward
      rest oldClause vivifiedClause strengthens vivifiedSat

theorem ay_failed_viv_composed_equisat
    (rest : AyFailedVivFormula)
    (literal : AyFailedVivLiteral)
    (oldClause vivifiedClause : AyFailedVivClause) :
    AyFailedVivProbe rest literal ->
    AyFailedVivSideWitness rest literal oldClause vivifiedClause ->
    AyFailedVivStrengtheningWitness oldClause vivifiedClause ->
    AyFailedVivEquisat
      (AyFailedVivWithClause rest oldClause)
      (AyFailedVivWithClause rest vivifiedClause) :=
  fun failed side strengthens result keep =>
    keep
      (ay_failed_viv_composed_forward
        rest literal oldClause vivifiedClause failed side)
      (ay_failed_viv_composed_backward
        rest oldClause vivifiedClause strengthens)
