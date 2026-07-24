-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Algebra for composing SAT clause-deletion transformations.

def AyDeletionConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyDeletionForward (before : Prop) (after : Prop) :=
  before -> after

def AyDeletionBackward (before : Prop) (after : Prop) :=
  after -> before

def AyDeletionEquisat (before : Prop) (after : Prop) :=
  AyDeletionConj
    (AyDeletionForward before after)
    (AyDeletionBackward before after)

theorem ay_deletion_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyDeletionConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_deletion_forward
    (before : Prop) (after : Prop) :
    AyDeletionEquisat before after -> AyDeletionForward before after := by
  intro eqdel
  exact eqdel (AyDeletionForward before after)
    (fun forward _backward => forward)

theorem ay_deletion_backward
    (before : Prop) (after : Prop) :
    AyDeletionEquisat before after -> AyDeletionBackward before after := by
  intro eqdel
  exact eqdel (AyDeletionBackward before after)
    (fun _forward backward => backward)

theorem ay_deletion_forward_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyDeletionForward a b ->
    AyDeletionForward b c ->
    AyDeletionForward a c := by
  intro ab
  intro bc
  intro ha
  exact bc (ab ha)

theorem ay_deletion_backward_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyDeletionBackward a b ->
    AyDeletionBackward b c ->
    AyDeletionBackward a c := by
  intro ba
  intro cb
  intro hc
  exact ba (cb hc)

def AyForcedDeletionBefore (clause : Prop) (rest : Prop) :=
  AyDeletionConj clause rest

def AyForcedDeletionAfter (rest : Prop) :=
  rest

theorem ay_forced_deletion_forward
    (clause : Prop) (rest : Prop) :
    AyForcedDeletionBefore clause rest ->
    AyForcedDeletionAfter rest := by
  intro full
  exact full rest (fun _clause_sat rest_sat => rest_sat)

theorem ay_forced_deletion_backward
    (clause : Prop) (rest : Prop) :
    (rest -> clause) ->
    AyForcedDeletionAfter rest ->
    AyForcedDeletionBefore clause rest := by
  intro forced
  intro rest_sat
  exact ay_deletion_conj_intro clause rest (forced rest_sat) rest_sat

theorem ay_forced_deletion_equisat
    (clause : Prop) (rest : Prop) :
    (rest -> clause) ->
    AyDeletionEquisat
      (AyForcedDeletionBefore clause rest)
      (AyForcedDeletionAfter rest) := by
  intro forced
  exact ay_deletion_conj_intro
    (AyForcedDeletionBefore clause rest -> AyForcedDeletionAfter rest)
    (AyForcedDeletionAfter rest -> AyForcedDeletionBefore clause rest)
    (ay_forced_deletion_forward clause rest)
    (ay_forced_deletion_backward clause rest forced)

theorem ay_two_forced_deletions_forward
    (firstClause : Prop) (secondClause : Prop) (rest : Prop) :
    AyDeletionConj firstClause (AyDeletionConj secondClause rest) ->
    rest := by
  intro full
  exact full rest
    (fun _firstSat tail =>
      tail rest (fun _secondSat restSat => restSat))

theorem ay_two_forced_deletions_backward
    (firstClause : Prop) (secondClause : Prop) (rest : Prop) :
    (AyDeletionConj secondClause rest -> firstClause) ->
    (rest -> secondClause) ->
    rest ->
    AyDeletionConj firstClause (AyDeletionConj secondClause rest) := by
  intro firstForced
  intro secondForced
  intro restSat
  exact ay_deletion_conj_intro firstClause
    (AyDeletionConj secondClause rest)
    (firstForced
      (ay_deletion_conj_intro secondClause rest
        (secondForced restSat) restSat))
    (ay_deletion_conj_intro secondClause rest
      (secondForced restSat) restSat)
