-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained assumption/core minimization certificate kernels.
-- Propositions stand for satisfiable formula fragments and assumption sets;
-- conflict witnesses are functions from a formula plus assumptions to False.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyConflictWitness (formula : Prop) (assumptions : Prop) :=
  formula -> assumptions -> False

def AyDroppedAssumptionProjection
    (fullAssumptions : Prop) (coreAssumptions : Prop) :=
  fullAssumptions -> coreAssumptions

def AyCoreCertificate
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :=
  AyConj
    (AyDroppedAssumptionProjection fullAssumptions coreAssumptions)
    (AyConflictWitness formula coreAssumptions)

def AyCoreTransportCertificate
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :=
  AyConj
    (AyEquisat originalFormula preprocessedFormula)
    (AyCoreCertificate preprocessedFormula fullAssumptions coreAssumptions)

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

theorem ay_core_certificate_projection
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    AyDroppedAssumptionProjection fullAssumptions coreAssumptions := by
  intro certificate
  exact ay_conj_left
    (AyDroppedAssumptionProjection fullAssumptions coreAssumptions)
    (AyConflictWitness formula coreAssumptions)
    certificate

theorem ay_core_certificate_conflict
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    AyConflictWitness formula coreAssumptions := by
  intro certificate
  exact certificate (AyConflictWitness formula coreAssumptions)
    (fun _project conflict => conflict)

theorem ay_unsat_core_project_dropped_assumptions
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    fullAssumptions -> coreAssumptions := by
  intro certificate
  exact ay_core_certificate_projection
    formula fullAssumptions coreAssumptions certificate

theorem ay_conflict_witness_reconstruct_full
    (formula : Prop) (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyDroppedAssumptionProjection fullAssumptions coreAssumptions ->
    AyConflictWitness formula coreAssumptions ->
    AyConflictWitness formula fullAssumptions := by
  intro project
  intro coreConflict
  intro hformula
  intro hfull
  exact coreConflict hformula (project hfull)

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

theorem ay_conflict_monotone_strengthening
    (formula : Prop) (weakerAssumptions : Prop) (strongerAssumptions : Prop) :
    (strongerAssumptions -> weakerAssumptions) ->
    AyConflictWitness formula weakerAssumptions ->
    AyConflictWitness formula strongerAssumptions := by
  intro stronger_to_weaker
  intro weakerConflict
  intro hformula
  intro hstronger
  exact weakerConflict hformula (stronger_to_weaker hstronger)

theorem ay_core_minimization_monotone
    (formula : Prop) (fullAssumptions : Prop)
    (coreAssumptions : Prop) (smallerCoreAssumptions : Prop) :
    AyDroppedAssumptionProjection fullAssumptions coreAssumptions ->
    AyDroppedAssumptionProjection coreAssumptions smallerCoreAssumptions ->
    AyConflictWitness formula smallerCoreAssumptions ->
    AyConflictWitness formula fullAssumptions := by
  intro full_to_core
  intro core_to_smaller
  intro smallerConflict
  exact ay_conflict_monotone_strengthening
    formula
    smallerCoreAssumptions
    fullAssumptions
    (fun hfull => core_to_smaller (full_to_core hfull))
    smallerConflict

theorem ay_core_certificate_minimize
    (formula : Prop) (fullAssumptions : Prop)
    (coreAssumptions : Prop) (smallerCoreAssumptions : Prop) :
    AyDroppedAssumptionProjection coreAssumptions smallerCoreAssumptions ->
    AyConflictWitness formula smallerCoreAssumptions ->
    AyCoreCertificate formula fullAssumptions coreAssumptions ->
    AyCoreCertificate formula fullAssumptions smallerCoreAssumptions := by
  intro core_to_smaller
  intro smallerConflict
  intro certificate
  exact ay_conj_intro
    (AyDroppedAssumptionProjection fullAssumptions smallerCoreAssumptions)
    (AyConflictWitness formula smallerCoreAssumptions)
    (fun hfull =>
      core_to_smaller
        (ay_core_certificate_projection
          formula fullAssumptions coreAssumptions certificate hfull))
    smallerConflict

theorem ay_preprocessing_conflict_transport_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyConflictWitness preprocessedFormula assumptions ->
    AyConflictWitness originalFormula assumptions := by
  intro equisat
  intro preprocessedConflict
  intro horiginal
  intro hassumptions
  exact preprocessedConflict
    (ay_equisat_forward originalFormula preprocessedFormula equisat horiginal)
    hassumptions

theorem ay_preprocessing_conflict_transport_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyConflictWitness originalFormula assumptions ->
    AyConflictWitness preprocessedFormula assumptions := by
  intro equisat
  intro originalConflict
  intro hpreprocessed
  intro hassumptions
  exact originalConflict
    (ay_equisat_backward originalFormula preprocessedFormula equisat hpreprocessed)
    hassumptions

theorem ay_preprocessing_core_certificate_transport_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyCoreCertificate preprocessedFormula fullAssumptions coreAssumptions ->
    AyCoreCertificate originalFormula fullAssumptions coreAssumptions := by
  intro equisat
  intro certificate
  exact ay_conj_intro
    (AyDroppedAssumptionProjection fullAssumptions coreAssumptions)
    (AyConflictWitness originalFormula coreAssumptions)
    (ay_core_certificate_projection
      preprocessedFormula fullAssumptions coreAssumptions certificate)
    (ay_preprocessing_conflict_transport_forward
      originalFormula preprocessedFormula coreAssumptions equisat
      (ay_core_certificate_conflict
        preprocessedFormula fullAssumptions coreAssumptions certificate))

theorem ay_preprocessing_core_certificate_transport_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyEquisat originalFormula preprocessedFormula ->
    AyCoreCertificate originalFormula fullAssumptions coreAssumptions ->
    AyCoreCertificate preprocessedFormula fullAssumptions coreAssumptions := by
  intro equisat
  intro certificate
  exact ay_conj_intro
    (AyDroppedAssumptionProjection fullAssumptions coreAssumptions)
    (AyConflictWitness preprocessedFormula coreAssumptions)
    (ay_core_certificate_projection
      originalFormula fullAssumptions coreAssumptions certificate)
    (ay_preprocessing_conflict_transport_backward
      originalFormula preprocessedFormula coreAssumptions equisat
      (ay_core_certificate_conflict
        originalFormula fullAssumptions coreAssumptions certificate))

theorem ay_transport_certificate_project_equisat
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreTransportCertificate
      originalFormula preprocessedFormula fullAssumptions coreAssumptions ->
    AyEquisat originalFormula preprocessedFormula := by
  intro transport
  exact ay_conj_left
    (AyEquisat originalFormula preprocessedFormula)
    (AyCoreCertificate
      preprocessedFormula fullAssumptions coreAssumptions)
    transport

theorem ay_transport_certificate_project_core
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreTransportCertificate
      originalFormula preprocessedFormula fullAssumptions coreAssumptions ->
    AyCoreCertificate preprocessedFormula fullAssumptions coreAssumptions := by
  intro transport
  exact transport
    (AyCoreCertificate
      preprocessedFormula fullAssumptions coreAssumptions)
    (fun _equisat certificate => certificate)

theorem ay_transport_certificate_conflict_on_original
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (fullAssumptions : Prop) (coreAssumptions : Prop) :
    AyCoreTransportCertificate
      originalFormula preprocessedFormula fullAssumptions coreAssumptions ->
    AyConflictWitness originalFormula fullAssumptions := by
  intro transport
  exact ay_core_certificate_reconstruct_conflict
    originalFormula fullAssumptions coreAssumptions
    (ay_preprocessing_core_certificate_transport_forward
      originalFormula preprocessedFormula fullAssumptions coreAssumptions
      (ay_transport_certificate_project_equisat
        originalFormula preprocessedFormula
        fullAssumptions coreAssumptions transport)
      (ay_transport_certificate_project_core
        originalFormula preprocessedFormula
        fullAssumptions coreAssumptions transport))
