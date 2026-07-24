-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for RAT trace compression.
-- The uncompressed trace adds candidate A, derives B using A, then deletes A.
-- With checked witnesses for the addition and derivation, the visible result
-- can be compressed to a direct trace from the existing clauses to B.

def AyRatCompressConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyRatCompressEquisat (original : Prop) (compressed : Prop) :=
  AyRatCompressConj (original -> compressed) (compressed -> original)

def AyRatCompressStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyRatCompressAdded (existing : Prop) (candidateA : Prop) :=
  AyRatCompressConj existing candidateA

def AyRatCompressUncompressedTrace
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :=
  AyRatCompressConj (AyRatCompressAdded existing candidateA) derivedB

def AyRatCompressDirectTrace
    (existing : Prop) (derivedB : Prop) :=
  AyRatCompressConj existing derivedB

theorem ay_rat_compress_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyRatCompressConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_rat_compress_conj_left
    (left : Prop) (right : Prop) :
    AyRatCompressConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_rat_compress_conj_right
    (left : Prop) (right : Prop) :
    AyRatCompressConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_rat_compress_add_candidate
    (existing : Prop) (candidateA : Prop) :
    AyRatCompressStep existing candidateA ->
    AyRatCompressStep existing (AyRatCompressAdded existing candidateA) := by
  intro addA
  intro existing_sat
  exact ay_rat_compress_conj_intro existing candidateA
    existing_sat
    (addA existing_sat)

theorem ay_rat_compress_derive_after_add
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressStep existing candidateA ->
    AyRatCompressStep (AyRatCompressAdded existing candidateA) derivedB ->
    AyRatCompressStep
      existing
      (AyRatCompressUncompressedTrace existing candidateA derivedB) := by
  intro addA
  intro deriveB
  intro existing_sat
  let added := ay_rat_compress_add_candidate existing candidateA addA existing_sat
  exact ay_rat_compress_conj_intro
    (AyRatCompressAdded existing candidateA)
    derivedB
    added
    (deriveB added)

theorem ay_rat_compress_delete_candidate_projection
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressUncompressedTrace existing candidateA derivedB ->
    AyRatCompressDirectTrace existing derivedB := by
  intro trace
  exact ay_rat_compress_conj_intro existing derivedB
    (ay_rat_compress_conj_left existing candidateA
      (ay_rat_compress_conj_left
        (AyRatCompressAdded existing candidateA)
        derivedB
        trace))
    (ay_rat_compress_conj_right
      (AyRatCompressAdded existing candidateA)
      derivedB
      trace)

theorem ay_rat_compress_direct_derive
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressStep existing candidateA ->
    AyRatCompressStep (AyRatCompressAdded existing candidateA) derivedB ->
    AyRatCompressStep existing derivedB := by
  intro addA
  intro deriveB
  intro existing_sat
  exact ay_rat_compress_conj_right
    existing
    derivedB
    (ay_rat_compress_delete_candidate_projection existing candidateA derivedB
      (ay_rat_compress_derive_after_add existing candidateA derivedB
        addA
        deriveB
        existing_sat))

theorem ay_rat_compress_direct_trace
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressStep existing candidateA ->
    AyRatCompressStep (AyRatCompressAdded existing candidateA) derivedB ->
    AyRatCompressStep existing (AyRatCompressDirectTrace existing derivedB) := by
  intro addA
  intro deriveB
  intro existing_sat
  exact ay_rat_compress_conj_intro existing derivedB
    existing_sat
    (ay_rat_compress_direct_derive existing candidateA derivedB
      addA
      deriveB
      existing_sat)

theorem ay_rat_trace_compression_projection
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressUncompressedTrace existing candidateA derivedB ->
    AyRatCompressDirectTrace existing derivedB := by
  intro trace
  exact ay_rat_compress_delete_candidate_projection
    existing candidateA derivedB trace

theorem ay_rat_trace_compression_from_witnesses
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressStep existing candidateA ->
    AyRatCompressStep (AyRatCompressAdded existing candidateA) derivedB ->
    existing ->
    AyRatCompressDirectTrace existing derivedB := by
  intro addA
  intro deriveB
  intro existing_sat
  exact ay_rat_compress_direct_trace existing candidateA derivedB
    addA
    deriveB
    existing_sat

theorem ay_rat_compress_direct_trace_projection
    (existing : Prop) (derivedB : Prop) :
    AyRatCompressDirectTrace existing derivedB -> existing := by
  intro direct
  exact ay_rat_compress_conj_left existing derivedB direct

theorem ay_rat_compress_direct_trace_candidate
    (existing : Prop) (derivedB : Prop) :
    AyRatCompressDirectTrace existing derivedB -> derivedB := by
  intro direct
  exact ay_rat_compress_conj_right existing derivedB direct

theorem ay_rat_compressed_trace_equisat
    (existing : Prop) (candidateA : Prop) (derivedB : Prop) :
    AyRatCompressStep existing candidateA ->
    AyRatCompressStep (AyRatCompressAdded existing candidateA) derivedB ->
    AyRatCompressEquisat existing (AyRatCompressDirectTrace existing derivedB) := by
  intro addA
  intro deriveB
  exact ay_rat_compress_conj_intro
    (existing -> AyRatCompressDirectTrace existing derivedB)
    (AyRatCompressDirectTrace existing derivedB -> existing)
    (ay_rat_trace_compression_from_witnesses existing candidateA derivedB
      addA
      deriveB)
    (ay_rat_compress_direct_trace_projection existing derivedB)

