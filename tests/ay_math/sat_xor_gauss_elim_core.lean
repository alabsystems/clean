-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for XOR/Gaussian-elimination style reasoning
-- as a SAT preprocessing certificate skeleton. Parity rows are abstract
-- propositions; row-combination and auxiliary reconstruction are explicit
-- witnesses. The CNF/Tseitin interface is represented by equisat transport.

def AyXorConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyXorDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyXorEquisat (before : Prop) (after : Prop) :=
  AyXorConj (before -> after) (after -> before)

def AyXorParityRow (row : Prop) :=
  row

def AyXorRowSystem (first : Prop) (second : Prop) :=
  AyXorConj first second

def AyXorCombinedSystem (kept : Prop) (combined : Prop) :=
  AyXorConj kept combined

def AyXorRowImplication (source : Prop) (target : Prop) :=
  source -> target

def AyXorRowCombinationWitness
    (first : Prop) (second : Prop) (combined : Prop) :=
  first -> second -> combined

def AyXorAuxElimBefore
    (context : Prop) (auxRow : Prop) (pivotRow : Prop) :=
  AyXorConj context (AyXorConj auxRow pivotRow)

def AyXorAuxElimAfter
    (context : Prop) (combinedRow : Prop) :=
  AyXorConj context combinedRow

def AyXorAuxReconstructionWitness
    (context : Prop) (combinedRow : Prop) (auxRow : Prop) (pivotRow : Prop) :=
  context -> combinedRow -> AyXorConj auxRow pivotRow

def AyXorCnfInterface
    (cnfFormula : Prop) (xorFormula : Prop) :=
  AyXorEquisat cnfFormula xorFormula

theorem ay_xor_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyXorConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_xor_conj_left
    (left : Prop) (right : Prop) :
    AyXorConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_xor_conj_right
    (left : Prop) (right : Prop) :
    AyXorConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_xor_row_implication_apply
    (source : Prop) (target : Prop) :
    AyXorRowImplication source target ->
    AyXorParityRow source ->
    AyXorParityRow target :=
  fun implication sourceH =>
    implication sourceH

theorem ay_xor_row_combination_project
    (first : Prop) (second : Prop) (combined : Prop) :
    AyXorRowCombinationWitness first second combined ->
    AyXorRowSystem first second ->
    AyXorCombinedSystem second combined := by
  intro combine
  intro system
  exact system (AyXorCombinedSystem second combined)
    (fun firstH secondH =>
      ay_xor_conj_intro second combined
        secondH
        (combine firstH secondH))

theorem ay_xor_row_combination_reconstruct
    (first : Prop) (second : Prop) (combined : Prop) :
    (second -> combined -> first) ->
    AyXorCombinedSystem second combined ->
    AyXorRowSystem first second := by
  intro reconstruct
  intro combinedSystem
  exact combinedSystem (AyXorRowSystem first second)
    (fun secondH combinedH =>
      ay_xor_conj_intro first second
        (reconstruct secondH combinedH)
        secondH)

theorem ay_xor_row_combination_equisat
    (first : Prop) (second : Prop) (combined : Prop) :
    AyXorRowCombinationWitness first second combined ->
    (second -> combined -> first) ->
    AyXorEquisat
      (AyXorRowSystem first second)
      (AyXorCombinedSystem second combined) :=
  fun combine reconstruct result keep =>
    keep
      (ay_xor_row_combination_project first second combined combine)
      (ay_xor_row_combination_reconstruct
        first second combined reconstruct)

theorem ay_xor_aux_elim_projection
    (context : Prop) (auxRow : Prop)
    (pivotRow : Prop) (combinedRow : Prop) :
    AyXorRowCombinationWitness auxRow pivotRow combinedRow ->
    AyXorAuxElimBefore context auxRow pivotRow ->
    AyXorAuxElimAfter context combinedRow := by
  intro combine
  intro before
  exact before (AyXorAuxElimAfter context combinedRow)
    (fun contextH rows =>
      rows (AyXorAuxElimAfter context combinedRow)
        (fun auxH pivotH =>
          ay_xor_conj_intro context combinedRow
            contextH
            (combine auxH pivotH)))

theorem ay_xor_aux_elim_reconstruction
    (context : Prop) (auxRow : Prop)
    (pivotRow : Prop) (combinedRow : Prop) :
    AyXorAuxReconstructionWitness context combinedRow auxRow pivotRow ->
    AyXorAuxElimAfter context combinedRow ->
    AyXorAuxElimBefore context auxRow pivotRow := by
  intro reconstruct
  intro after
  exact after (AyXorAuxElimBefore context auxRow pivotRow)
    (fun contextH combinedH =>
      ay_xor_conj_intro context
        (AyXorConj auxRow pivotRow)
        contextH
        (reconstruct contextH combinedH))

theorem ay_xor_aux_elim_equisat
    (context : Prop) (auxRow : Prop)
    (pivotRow : Prop) (combinedRow : Prop) :
    AyXorRowCombinationWitness auxRow pivotRow combinedRow ->
    AyXorAuxReconstructionWitness context combinedRow auxRow pivotRow ->
    AyXorEquisat
      (AyXorAuxElimBefore context auxRow pivotRow)
      (AyXorAuxElimAfter context combinedRow) :=
  fun combine reconstruct result keep =>
    keep
      (ay_xor_aux_elim_projection
        context auxRow pivotRow combinedRow combine)
      (ay_xor_aux_elim_reconstruction
        context auxRow pivotRow combinedRow reconstruct)

theorem ay_xor_equisat_forward
    (before : Prop) (after : Prop) :
    AyXorEquisat before after -> before -> after := by
  intro equisat
  exact equisat (before -> after)
    (fun forward _backward => forward)

theorem ay_xor_equisat_backward
    (before : Prop) (after : Prop) :
    AyXorEquisat before after -> after -> before := by
  intro equisat
  exact equisat (after -> before)
    (fun _forward backward => backward)

theorem ay_xor_equisat_compose
    (first : Prop) (middle : Prop) (last : Prop) :
    AyXorEquisat first middle ->
    AyXorEquisat middle last ->
    AyXorEquisat first last :=
  fun firstMiddle middleLast result keep =>
    keep
      (fun firstH =>
        ay_xor_equisat_forward middle last middleLast
          (ay_xor_equisat_forward first middle firstMiddle firstH))
      (fun lastH =>
        ay_xor_equisat_backward first middle firstMiddle
          (ay_xor_equisat_backward middle last middleLast lastH))

theorem ay_xor_cnf_to_xor_projection
    (cnfFormula : Prop) (xorFormula : Prop) :
    AyXorCnfInterface cnfFormula xorFormula ->
    cnfFormula -> xorFormula :=
  fun interface cnfH =>
    ay_xor_equisat_forward cnfFormula xorFormula interface cnfH

theorem ay_xor_cnf_to_xor_reconstruction
    (cnfFormula : Prop) (xorFormula : Prop) :
    AyXorCnfInterface cnfFormula xorFormula ->
    xorFormula -> cnfFormula :=
  fun interface xorH =>
    ay_xor_equisat_backward cnfFormula xorFormula interface xorH

theorem ay_xor_cnf_transport_after_elim_forward
    (cnfBefore : Prop) (xorBefore : Prop) (xorAfter : Prop) :
    AyXorCnfInterface cnfBefore xorBefore ->
    AyXorEquisat xorBefore xorAfter ->
    cnfBefore -> xorAfter :=
  fun interface elim cnfH =>
    ay_xor_equisat_forward xorBefore xorAfter elim
      (ay_xor_cnf_to_xor_projection
        cnfBefore xorBefore interface cnfH)

theorem ay_xor_cnf_transport_after_elim_backward
    (cnfBefore : Prop) (xorBefore : Prop) (xorAfter : Prop) :
    AyXorCnfInterface cnfBefore xorBefore ->
    AyXorEquisat xorBefore xorAfter ->
    xorAfter -> cnfBefore :=
  fun interface elim xorAfterH =>
    ay_xor_cnf_to_xor_reconstruction
      cnfBefore xorBefore interface
      (ay_xor_equisat_backward xorBefore xorAfter elim xorAfterH)

theorem ay_xor_cnf_transport_after_elim_equisat
    (cnfBefore : Prop) (xorBefore : Prop) (xorAfter : Prop) :
    AyXorCnfInterface cnfBefore xorBefore ->
    AyXorEquisat xorBefore xorAfter ->
    AyXorEquisat cnfBefore xorAfter :=
  fun interface elim result keep =>
    keep
      (ay_xor_cnf_transport_after_elim_forward
        cnfBefore xorBefore xorAfter interface elim)
      (ay_xor_cnf_transport_after_elim_backward
        cnfBefore xorBefore xorAfter interface elim)

theorem ay_xor_tseitin_interface_transport
    (cnfBefore : Prop) (xorBefore : Prop)
    (context : Prop) (auxRow : Prop)
    (pivotRow : Prop) (combinedRow : Prop) :
    AyXorCnfInterface
      cnfBefore
      (AyXorAuxElimBefore context auxRow pivotRow) ->
    AyXorRowCombinationWitness auxRow pivotRow combinedRow ->
    AyXorAuxReconstructionWitness context combinedRow auxRow pivotRow ->
    AyXorEquisat cnfBefore (AyXorAuxElimAfter context combinedRow) := by
  intro interface
  intro combine
  intro reconstruct
  exact ay_xor_cnf_transport_after_elim_equisat
    cnfBefore
    (AyXorAuxElimBefore context auxRow pivotRow)
    (AyXorAuxElimAfter context combinedRow)
    interface
    (ay_xor_aux_elim_equisat
      context auxRow pivotRow combinedRow combine reconstruct)
