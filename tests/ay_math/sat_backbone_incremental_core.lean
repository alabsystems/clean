-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained backbone/incremental-assumption/core-minimization kernels.
-- Propositions stand for satisfiable formula fragments and assumption scopes.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyAssumedFormula (formula : Prop) (assumptions : Prop) :=
  AyConj formula assumptions

def AyFormulaWithUnit (formula : Prop) (unitLit : Prop) :=
  AyConj formula unitLit

def AyBackboneUnderAssumptions
    (formula : Prop) (assumptions : Prop) (unitLit : Prop) :=
  AyAssumedFormula formula assumptions -> unitLit

def AyScopeProjection (activeScope : Prop) (poppedScope : Prop) :=
  activeScope -> poppedScope

def AyConflictWitness (formula : Prop) (assumptions : Prop) :=
  formula -> assumptions -> False

def AyCoreCertificate
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :=
  AyConj
    (fullAssumptions -> coreAssumptions)
    (AyConflictWitness formula coreAssumptions)

def AyIncrementalBackboneCoreCertificate
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :=
  AyConj
    (AyScopeProjection activeScope poppedScope)
    (AyConj
      (AyBackboneUnderAssumptions formula poppedScope unitLit)
      (AyCoreCertificate formula poppedScope coreAssumptions))

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

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

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
  exact ay_conj_left
    (original -> transformed)
    (transformed -> original)
    equisat

theorem ay_equisat_backward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    transformed -> original := by
  intro equisat
  exact equisat (transformed -> original)
    (fun _forward backward => backward)

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (fun hfirst =>
      ay_equisat_forward middle last middle_last
        (ay_equisat_forward first middle first_middle hfirst))
    (fun hlast =>
      ay_equisat_backward first middle first_middle
        (ay_equisat_backward middle last middle_last hlast))

theorem ay_assumed_formula_project_formula
    (formula : Prop) (assumptions : Prop) :
    AyAssumedFormula formula assumptions ->
    formula := by
  intro assumed
  exact assumed formula
    (fun hformula _hassumptions => hformula)

theorem ay_assumed_formula_project_assumptions
    (formula : Prop) (assumptions : Prop) :
    AyAssumedFormula formula assumptions ->
    assumptions := by
  intro assumed
  exact assumed assumptions
    (fun _hformula hassumptions => hassumptions)

theorem ay_assumed_formula_intro
    (formula : Prop) (assumptions : Prop) :
    formula -> assumptions -> AyAssumedFormula formula assumptions := by
  intro hformula
  intro hassumptions
  exact ay_conj_intro formula assumptions hformula hassumptions

theorem ay_formula_with_unit_project_formula
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    formula := by
  intro with_unit
  exact with_unit formula
    (fun hformula _hunit => hformula)

theorem ay_formula_with_unit_project_unit
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    unitLit := by
  intro with_unit
  exact with_unit unitLit
    (fun _hformula hunit => hunit)

theorem ay_backbone_under_assumptions_add_unit_forward
    (formula : Prop) (assumptions : Prop) (unitLit : Prop) :
    AyBackboneUnderAssumptions formula assumptions unitLit ->
    AyAssumedFormula formula assumptions ->
    AyConj (AyAssumedFormula formula assumptions) unitLit := by
  intro backbone
  intro assumed
  exact ay_conj_intro
    (AyAssumedFormula formula assumptions)
    unitLit
    assumed
    (backbone assumed)

theorem ay_backbone_under_assumptions_add_unit_backward
    (formula : Prop) (assumptions : Prop) (unitLit : Prop) :
    AyConj (AyAssumedFormula formula assumptions) unitLit ->
    AyAssumedFormula formula assumptions := by
  intro with_unit
  exact with_unit (AyAssumedFormula formula assumptions)
    (fun assumed _hunit => assumed)

theorem ay_backbone_under_assumptions_add_unit_equisat
    (formula : Prop) (assumptions : Prop) (unitLit : Prop) :
    AyBackboneUnderAssumptions formula assumptions unitLit ->
    AyEquisat
      (AyAssumedFormula formula assumptions)
      (AyConj (AyAssumedFormula formula assumptions) unitLit) := by
  intro backbone
  exact ay_equisat_intro
    (AyAssumedFormula formula assumptions)
    (AyConj (AyAssumedFormula formula assumptions) unitLit)
    (ay_backbone_under_assumptions_add_unit_forward
      formula assumptions unitLit backbone)
    (ay_backbone_under_assumptions_add_unit_backward
      formula assumptions unitLit)

theorem ay_scope_projection_assumed_formula
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop) :
    AyScopeProjection activeScope poppedScope ->
    AyAssumedFormula formula activeScope ->
    AyAssumedFormula formula poppedScope := by
  intro project
  intro active
  exact ay_assumed_formula_intro formula poppedScope
    (ay_assumed_formula_project_formula formula activeScope active)
    (project
      (ay_assumed_formula_project_assumptions formula activeScope active))

theorem ay_backbone_after_popped_scope
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop) (unitLit : Prop) :
    AyScopeProjection activeScope poppedScope ->
    AyBackboneUnderAssumptions formula poppedScope unitLit ->
    AyBackboneUnderAssumptions formula activeScope unitLit := by
  intro project
  intro popped_backbone
  intro active
  exact popped_backbone
    (ay_scope_projection_assumed_formula
      formula activeScope poppedScope project active)

theorem ay_popped_scope_unit_add_equisat
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop) (unitLit : Prop) :
    AyScopeProjection activeScope poppedScope ->
    AyBackboneUnderAssumptions formula poppedScope unitLit ->
    AyEquisat
      (AyAssumedFormula formula activeScope)
      (AyConj (AyAssumedFormula formula activeScope) unitLit) := by
  intro project
  intro popped_backbone
  exact ay_backbone_under_assumptions_add_unit_equisat
    formula activeScope unitLit
    (ay_backbone_after_popped_scope
      formula activeScope poppedScope unitLit project popped_backbone)

theorem ay_core_certificate_projection
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    fullAssumptions -> coreAssumptions := by
  intro certificate
  exact certificate (fullAssumptions -> coreAssumptions)
    (fun project _conflict => project)

theorem ay_core_certificate_conflict
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    AyConflictWitness formula coreAssumptions := by
  intro certificate
  exact certificate (AyConflictWitness formula coreAssumptions)
    (fun _project conflict => conflict)

theorem ay_conflict_witness_reconstruct_full
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    (fullAssumptions -> coreAssumptions) ->
    AyConflictWitness formula coreAssumptions ->
    AyConflictWitness formula fullAssumptions := by
  intro project
  intro core_conflict
  intro hformula
  intro hfull
  exact core_conflict hformula (project hfull)

theorem ay_core_certificate_reconstruct_conflict
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    AyConflictWitness formula fullAssumptions := by
  intro certificate
  exact ay_conflict_witness_reconstruct_full
    formula fullAssumptions coreAssumptions
    (ay_core_certificate_projection
      formula fullAssumptions coreAssumptions certificate)
    (ay_core_certificate_conflict
      formula fullAssumptions coreAssumptions certificate)

theorem ay_core_project_after_popped_scope
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) :
    AyScopeProjection activeScope poppedScope ->
    AyCoreCertificate formula poppedScope coreAssumptions ->
    activeScope -> coreAssumptions := by
  intro active_to_popped
  intro certificate
  intro hactive
  exact ay_core_certificate_projection
    formula poppedScope coreAssumptions certificate
    (active_to_popped hactive)

theorem ay_core_conflict_after_popped_scope
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) :
    AyScopeProjection activeScope poppedScope ->
    AyCoreCertificate formula poppedScope coreAssumptions ->
    AyConflictWitness formula activeScope := by
  intro active_to_popped
  intro certificate
  exact ay_conflict_witness_reconstruct_full
    formula activeScope coreAssumptions
    (ay_core_project_after_popped_scope
      formula activeScope poppedScope coreAssumptions
      active_to_popped certificate)
    (ay_core_certificate_conflict
      formula poppedScope coreAssumptions certificate)

theorem ay_core_minimize_after_popped_scope
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (smallerCore : Prop) :
    AyScopeProjection activeScope poppedScope ->
    AyCoreCertificate formula poppedScope coreAssumptions ->
    (coreAssumptions -> smallerCore) ->
    AyConflictWitness formula smallerCore ->
    AyCoreCertificate formula activeScope smallerCore := by
  intro active_to_popped
  intro certificate
  intro core_to_smaller
  intro smaller_conflict
  exact ay_conj_intro
    (activeScope -> smallerCore)
    (AyConflictWitness formula smallerCore)
    (fun hactive =>
      core_to_smaller
        (ay_core_project_after_popped_scope
          formula activeScope poppedScope coreAssumptions
          active_to_popped certificate hactive))
    smaller_conflict

theorem ay_preprocessing_backbone_transport_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) (unitLit : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyBackboneUnderAssumptions preprocessedFormula assumptions unitLit ->
    AyBackboneUnderAssumptions originalFormula assumptions unitLit := by
  intro equisat
  intro preprocessed_backbone
  intro original_assumed
  exact preprocessed_backbone
    (ay_assumed_formula_intro preprocessedFormula assumptions
      (ay_equisat_forward originalFormula preprocessedFormula equisat
        (ay_assumed_formula_project_formula
          originalFormula assumptions original_assumed))
      (ay_assumed_formula_project_assumptions
        originalFormula assumptions original_assumed))

theorem ay_preprocessing_backbone_transport_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) (unitLit : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyBackboneUnderAssumptions originalFormula assumptions unitLit ->
    AyBackboneUnderAssumptions preprocessedFormula assumptions unitLit := by
  intro equisat
  intro original_backbone
  intro preprocessed_assumed
  exact original_backbone
    (ay_assumed_formula_intro originalFormula assumptions
      (ay_equisat_backward originalFormula preprocessedFormula equisat
        (ay_assumed_formula_project_formula
          preprocessedFormula assumptions preprocessed_assumed))
      (ay_assumed_formula_project_assumptions
        preprocessedFormula assumptions preprocessed_assumed))

theorem ay_preprocessing_conflict_transport_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyConflictWitness preprocessedFormula assumptions ->
    AyConflictWitness originalFormula assumptions := by
  intro equisat
  intro preprocessed_conflict
  intro horiginal
  intro hassumptions
  exact preprocessed_conflict
    (ay_equisat_forward originalFormula preprocessedFormula equisat horiginal)
    hassumptions

theorem ay_preprocessing_conflict_transport_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyConflictWitness originalFormula assumptions ->
    AyConflictWitness preprocessedFormula assumptions := by
  intro equisat
  intro original_conflict
  intro hpreprocessed
  intro hassumptions
  exact original_conflict
    (ay_equisat_backward originalFormula preprocessedFormula equisat hpreprocessed)
    hassumptions

theorem ay_preprocessing_core_transport_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyCoreCertificate preprocessedFormula fullAssumptions coreAssumptions ->
    AyCoreCertificate originalFormula fullAssumptions coreAssumptions := by
  intro equisat
  intro certificate
  exact ay_conj_intro
    (fullAssumptions -> coreAssumptions)
    (AyConflictWitness originalFormula coreAssumptions)
    (ay_core_certificate_projection
      preprocessedFormula fullAssumptions coreAssumptions certificate)
    (ay_preprocessing_conflict_transport_forward
      originalFormula preprocessedFormula coreAssumptions equisat
      (ay_core_certificate_conflict
        preprocessedFormula fullAssumptions coreAssumptions certificate))

theorem ay_preprocessing_core_transport_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyCoreCertificate originalFormula fullAssumptions coreAssumptions ->
    AyCoreCertificate preprocessedFormula fullAssumptions coreAssumptions := by
  intro equisat
  intro certificate
  exact ay_conj_intro
    (fullAssumptions -> coreAssumptions)
    (AyConflictWitness preprocessedFormula coreAssumptions)
    (ay_core_certificate_projection
      originalFormula fullAssumptions coreAssumptions certificate)
    (ay_preprocessing_conflict_transport_backward
      originalFormula preprocessedFormula coreAssumptions equisat
      (ay_core_certificate_conflict
        originalFormula fullAssumptions coreAssumptions certificate))

theorem ay_incremental_certificate_project_scope
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyIncrementalBackboneCoreCertificate
      formula activeScope poppedScope coreAssumptions unitLit ->
    AyScopeProjection activeScope poppedScope := by
  intro certificate
  exact certificate (AyScopeProjection activeScope poppedScope)
    (fun scope_project _tail => scope_project)

theorem ay_incremental_certificate_project_backbone
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyIncrementalBackboneCoreCertificate
      formula activeScope poppedScope coreAssumptions unitLit ->
    AyBackboneUnderAssumptions formula poppedScope unitLit := by
  intro certificate
  exact certificate (AyBackboneUnderAssumptions formula poppedScope unitLit)
    (fun _scope_project tail =>
      tail (AyBackboneUnderAssumptions formula poppedScope unitLit)
        (fun backbone _core => backbone))

theorem ay_incremental_certificate_project_core
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyIncrementalBackboneCoreCertificate
      formula activeScope poppedScope coreAssumptions unitLit ->
    AyCoreCertificate formula poppedScope coreAssumptions := by
  intro certificate
  exact certificate (AyCoreCertificate formula poppedScope coreAssumptions)
    (fun _scope_project tail =>
      tail (AyCoreCertificate formula poppedScope coreAssumptions)
        (fun _backbone core => core))

theorem ay_incremental_certificate_active_backbone
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyIncrementalBackboneCoreCertificate
      formula activeScope poppedScope coreAssumptions unitLit ->
    AyBackboneUnderAssumptions formula activeScope unitLit := by
  intro certificate
  exact ay_backbone_after_popped_scope
    formula activeScope poppedScope unitLit
    (ay_incremental_certificate_project_scope
      formula activeScope poppedScope coreAssumptions unitLit certificate)
    (ay_incremental_certificate_project_backbone
      formula activeScope poppedScope coreAssumptions unitLit certificate)

theorem ay_incremental_certificate_active_conflict
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyIncrementalBackboneCoreCertificate
      formula activeScope poppedScope coreAssumptions unitLit ->
    AyConflictWitness formula activeScope := by
  intro certificate
  exact ay_core_conflict_after_popped_scope
    formula activeScope poppedScope coreAssumptions
    (ay_incremental_certificate_project_scope
      formula activeScope poppedScope coreAssumptions unitLit certificate)
    (ay_incremental_certificate_project_core
      formula activeScope poppedScope coreAssumptions unitLit certificate)

theorem ay_incremental_certificate_active_unit_equisat
    (formula : Prop) (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyIncrementalBackboneCoreCertificate
      formula activeScope poppedScope coreAssumptions unitLit ->
    AyEquisat
      (AyAssumedFormula formula activeScope)
      (AyConj (AyAssumedFormula formula activeScope) unitLit) := by
  intro certificate
  exact ay_backbone_under_assumptions_add_unit_equisat
    formula activeScope unitLit
    (ay_incremental_certificate_active_backbone
      formula activeScope poppedScope coreAssumptions unitLit certificate)

theorem ay_incremental_preprocessed_certificate_to_original
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (activeScope : Prop) (poppedScope : Prop)
    (coreAssumptions : Prop) (unitLit : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyIncrementalBackboneCoreCertificate
      preprocessedFormula activeScope poppedScope coreAssumptions unitLit ->
    AyIncrementalBackboneCoreCertificate
      originalFormula activeScope poppedScope coreAssumptions unitLit := by
  intro equisat
  intro certificate
  exact ay_conj_intro
    (AyScopeProjection activeScope poppedScope)
    (AyConj
      (AyBackboneUnderAssumptions originalFormula poppedScope unitLit)
      (AyCoreCertificate originalFormula poppedScope coreAssumptions))
    (ay_incremental_certificate_project_scope
      preprocessedFormula activeScope poppedScope coreAssumptions unitLit
      certificate)
    (ay_conj_intro
      (AyBackboneUnderAssumptions originalFormula poppedScope unitLit)
      (AyCoreCertificate originalFormula poppedScope coreAssumptions)
      (ay_preprocessing_backbone_transport_forward
        originalFormula preprocessedFormula poppedScope unitLit equisat
        (ay_incremental_certificate_project_backbone
          preprocessedFormula activeScope poppedScope coreAssumptions unitLit
          certificate))
      (ay_preprocessing_core_transport_forward
        originalFormula preprocessedFormula poppedScope coreAssumptions equisat
        (ay_incremental_certificate_project_core
          preprocessedFormula activeScope poppedScope coreAssumptions unitLit
          certificate)))
