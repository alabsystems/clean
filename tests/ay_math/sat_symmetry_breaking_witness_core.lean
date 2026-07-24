-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for symmetry-breaking clauses under explicit
-- canonical representative / reconstruction witnesses. The package is
-- self-contained and uses Church encodings for conjunction, disjunction,
-- and equisatisfiability.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AySymmetryOriginal (base : Prop) :=
  base

def AySymmetryBroken (base : Prop) (symBreak : Prop) :=
  AyConj base symBreak

def AyCanonicalWitness (base : Prop) (symBreak : Prop) :=
  base -> AySymmetryBroken base symBreak

def AyModelTransport (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyVisibleSymmetryWitness
    (base : Prop) (symBreak : Prop) (certificate : Prop) :=
  AyConj base (AyConj symBreak certificate)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

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

theorem ay_symmetry_break_projection
    (base : Prop) (symBreak : Prop) :
    AySymmetryBroken base symBreak ->
    AySymmetryOriginal base := by
  intro broken
  exact broken base
    (fun hbase _hsym => hbase)

theorem ay_symmetry_break_reconstruction
    (base : Prop) (symBreak : Prop) :
    AyCanonicalWitness base symBreak ->
    AySymmetryOriginal base ->
    AySymmetryBroken base symBreak := by
  intro canonical
  intro hbase
  exact canonical hbase

theorem ay_symmetry_break_equisat
    (base : Prop) (symBreak : Prop) :
    AyCanonicalWitness base symBreak ->
    AyEquisat
      (AySymmetryOriginal base)
      (AySymmetryBroken base symBreak) := by
  intro canonical
  exact ay_equisat_intro
    (AySymmetryOriginal base)
    (AySymmetryBroken base symBreak)
    (ay_symmetry_break_reconstruction base symBreak canonical)
    (ay_symmetry_break_projection base symBreak)

theorem ay_symmetry_transport_forward
    (base : Prop) (symBreak : Prop) :
    AyCanonicalWitness base symBreak ->
    AySymmetryOriginal base ->
    AySymmetryBroken base symBreak := by
  intro canonical
  exact ay_symmetry_break_reconstruction base symBreak canonical

theorem ay_symmetry_transport_backward
    (base : Prop) (symBreak : Prop) :
    AySymmetryBroken base symBreak ->
    AySymmetryOriginal base := by
  exact ay_symmetry_break_projection base symBreak

theorem ay_symmetry_model_transport
    (base : Prop) (symBreak : Prop) :
    AyCanonicalWitness base symBreak ->
    AyModelTransport
      (AySymmetryOriginal base)
      (AySymmetryBroken base symBreak) := by
  intro canonical
  exact ay_conj_intro
    (AySymmetryOriginal base -> AySymmetryBroken base symBreak)
    (AySymmetryBroken base symBreak -> AySymmetryOriginal base)
    (ay_symmetry_transport_forward base symBreak canonical)
    (ay_symmetry_transport_backward base symBreak)

theorem ay_symmetry_visible_project_base
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    AyVisibleSymmetryWitness base symBreak certificate ->
    base := by
  intro visible
  exact visible base
    (fun hbase _tail => hbase)

theorem ay_symmetry_visible_project_break
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    AyVisibleSymmetryWitness base symBreak certificate ->
    symBreak := by
  intro visible
  exact visible symBreak
    (fun _hbase tail =>
      tail symBreak
        (fun hsym _hcertificate => hsym))

theorem ay_symmetry_visible_project_certificate
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    AyVisibleSymmetryWitness base symBreak certificate ->
    certificate := by
  intro visible
  exact visible certificate
    (fun _hbase tail =>
      tail certificate
        (fun _hsym hcertificate => hcertificate))

theorem ay_symmetry_visible_reconstruct
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    base ->
    symBreak ->
    certificate ->
    AyVisibleSymmetryWitness base symBreak certificate := by
  intro hbase
  intro hsym
  intro hcertificate
  exact ay_conj_intro base (AyConj symBreak certificate)
    hbase
    (ay_conj_intro symBreak certificate hsym hcertificate)

theorem ay_symmetry_visible_from_canonical
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    AyCanonicalWitness base symBreak ->
    (base -> certificate) ->
    base ->
    AyVisibleSymmetryWitness base symBreak certificate := by
  intro canonical
  intro certificate_witness
  intro hbase
  exact canonical hbase (AyVisibleSymmetryWitness base symBreak certificate)
    (fun hbase_again hsym =>
      ay_symmetry_visible_reconstruct
        base symBreak certificate
        hbase_again
        hsym
        (certificate_witness hbase))

theorem ay_symmetry_visible_to_broken
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    AyVisibleSymmetryWitness base symBreak certificate ->
    AySymmetryBroken base symBreak := by
  intro visible
  exact ay_conj_intro base symBreak
    (ay_symmetry_visible_project_base base symBreak certificate visible)
    (ay_symmetry_visible_project_break base symBreak certificate visible)

theorem ay_symmetry_visible_transport_pair
    (base : Prop) (symBreak : Prop) (certificate : Prop) :
    AyCanonicalWitness base symBreak ->
    (base -> certificate) ->
    AyConj
      (AySymmetryOriginal base ->
        AyVisibleSymmetryWitness base symBreak certificate)
      (AyVisibleSymmetryWitness base symBreak certificate ->
        AySymmetryOriginal base) := by
  intro canonical
  intro certificate_witness
  exact ay_conj_intro
    (AySymmetryOriginal base ->
      AyVisibleSymmetryWitness base symBreak certificate)
    (AyVisibleSymmetryWitness base symBreak certificate ->
      AySymmetryOriginal base)
    (ay_symmetry_visible_from_canonical
      base symBreak certificate canonical certificate_witness)
    (ay_symmetry_visible_project_base base symBreak certificate)

theorem ay_symmetry_choice_left_preserves_transport
    (base : Prop) (symBreak : Prop) (fallback : Prop) :
    AyCanonicalWitness base symBreak ->
    AyDisj base fallback ->
    AyDisj (AySymmetryBroken base symBreak) fallback := by
  intro canonical
  intro choice
  intro result
  intro broken_to_result
  intro fallback_to_result
  exact choice result
    (fun hbase => broken_to_result (canonical hbase))
    fallback_to_result

theorem ay_symmetry_choice_right_preserves_transport
    (base : Prop) (symBreak : Prop) (fallback : Prop) :
    AyDisj fallback base ->
    AyCanonicalWitness base symBreak ->
    AyDisj fallback (AySymmetryBroken base symBreak) := by
  intro choice
  intro canonical
  intro result
  intro fallback_to_result
  intro broken_to_result
  exact choice result
    fallback_to_result
    (fun hbase => broken_to_result (canonical hbase))
