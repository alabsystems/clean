-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction for watched-literal BCP soundness. Watched clauses are
-- modeled by two watched literals plus a residual clause; movement, unit
-- discovery, conflict discovery, and propagation are related to the abstract
-- unit-propagation certificate.

def AyWLBDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyWLBConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyWLBEquisat (before : Prop) (after : Prop) :=
  AyWLBConj (before -> after) (after -> before)

def AyWLBClause (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWLBDisj watchA (AyWLBDisj watchB residual)

def AyWLBWatchedClause
    (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWLBClause watchA watchB residual

def AyWLBAbstractClause
    (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWLBClause watchA watchB residual

def AyWLBWatchMoveCertificate (oldWatch : Prop) (newWatch : Prop) :=
  AyWLBConj (oldWatch -> newWatch) (newWatch -> oldWatch)

def AyWLBUnitCertificate
    (watchA : Prop) (watchB : Prop) (unit : Prop) :=
  AyWLBConj (Not watchA) (AyWLBConj (Not watchB) unit)

def AyWLBConflictCertificate (watchA : Prop) (watchB : Prop) :=
  AyWLBConj (Not watchA) (Not watchB)

def AyWLBPropagationResult (unit : Prop) :=
  unit

def AyWLBAbstractUnitCertificate
    (watchA : Prop) (watchB : Prop) (unit : Prop) :=
  AyWLBConj
    (AyWLBClause watchA watchB unit)
    (AyWLBUnitCertificate watchA watchB unit)

theorem ay_wlb_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyWLBConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_wlb_disj_left
    (p : Prop) (q : Prop) :
    p -> AyWLBDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_wlb_disj_right
    (p : Prop) (q : Prop) :
    q -> AyWLBDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_wlb_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyWLBEquisat before after := by
  intro forward
  intro backward
  exact ay_wlb_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_wlb_move_old_to_new_forward
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop) :
    AyWLBWatchMoveCertificate oldWatch newWatch ->
    AyWLBWatchedClause oldWatch otherWatch residual ->
    AyWLBWatchedClause newWatch otherWatch residual := by
  intro move_cert
  intro clause
  exact clause (AyWLBWatchedClause newWatch otherWatch residual)
    (fun hold =>
      ay_wlb_disj_left newWatch (AyWLBDisj otherWatch residual)
        (move_cert newWatch (fun old_to_new _new_to_old => old_to_new hold)))
    (fun tail =>
      ay_wlb_disj_right newWatch (AyWLBDisj otherWatch residual) tail)

theorem ay_wlb_move_new_to_old_backward
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop) :
    AyWLBWatchMoveCertificate oldWatch newWatch ->
    AyWLBWatchedClause newWatch otherWatch residual ->
    AyWLBWatchedClause oldWatch otherWatch residual := by
  intro move_cert
  intro clause
  exact clause (AyWLBWatchedClause oldWatch otherWatch residual)
    (fun hnew =>
      ay_wlb_disj_left oldWatch (AyWLBDisj otherWatch residual)
        (move_cert oldWatch (fun _old_to_new new_to_old => new_to_old hnew)))
    (fun tail =>
      ay_wlb_disj_right oldWatch (AyWLBDisj otherWatch residual) tail)

theorem ay_wlb_watch_movement_preserves_clause
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop) :
    AyWLBWatchMoveCertificate oldWatch newWatch ->
    AyWLBEquisat
      (AyWLBWatchedClause oldWatch otherWatch residual)
      (AyWLBWatchedClause newWatch otherWatch residual) := by
  intro move_cert
  exact ay_wlb_equisat_intro
    (AyWLBWatchedClause oldWatch otherWatch residual)
    (AyWLBWatchedClause newWatch otherWatch residual)
    (ay_wlb_move_old_to_new_forward
      oldWatch newWatch otherWatch residual move_cert)
    (ay_wlb_move_new_to_old_backward
      oldWatch newWatch otherWatch residual move_cert)

theorem ay_wlb_clause_to_abstract
    (watchA : Prop) (watchB : Prop) (residual : Prop) :
    AyWLBWatchedClause watchA watchB residual ->
    AyWLBAbstractClause watchA watchB residual := by
  intro clause
  exact clause

theorem ay_wlb_abstract_to_watched
    (watchA : Prop) (watchB : Prop) (residual : Prop) :
    AyWLBAbstractClause watchA watchB residual ->
    AyWLBWatchedClause watchA watchB residual := by
  intro clause
  exact clause

theorem ay_wlb_watched_abstract_equisat
    (watchA : Prop) (watchB : Prop) (residual : Prop) :
    AyWLBEquisat
      (AyWLBWatchedClause watchA watchB residual)
      (AyWLBAbstractClause watchA watchB residual) := by
  exact ay_wlb_equisat_intro
    (AyWLBWatchedClause watchA watchB residual)
    (AyWLBAbstractClause watchA watchB residual)
    (ay_wlb_clause_to_abstract watchA watchB residual)
    (ay_wlb_abstract_to_watched watchA watchB residual)

theorem ay_wlb_unit_certificate_intro
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    Not watchA ->
    Not watchB ->
    unit ->
    AyWLBUnitCertificate watchA watchB unit := by
  intro notA
  intro notB
  intro hunit
  exact ay_wlb_conj_intro
    (Not watchA)
    (AyWLBConj (Not watchB) unit)
    notA
    (ay_wlb_conj_intro (Not watchB) unit notB hunit)

theorem ay_wlb_unit_discovery_sound
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWLBClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    unit := by
  intro clause
  intro notA
  intro notB
  exact clause unit
    (fun hwatchA => False.elim (notA hwatchA))
    (fun tail =>
      tail unit
        (fun hwatchB => False.elim (notB hwatchB))
        (fun hunit => hunit))

theorem ay_wlb_conflict_discovery_sound
    (watchA : Prop) (watchB : Prop) :
    AyWLBClause watchA watchB False ->
    AyWLBConflictCertificate watchA watchB ->
    False := by
  intro clause
  intro conflict
  exact conflict False
    (fun notA notB =>
      clause False
        (fun hwatchA => notA hwatchA)
        (fun tail =>
          tail False
            (fun hwatchB => notB hwatchB)
            (fun impossible => impossible)))

theorem ay_wlb_abstract_unit_certificate_intro
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWLBClause watchA watchB unit ->
    AyWLBUnitCertificate watchA watchB unit ->
    AyWLBAbstractUnitCertificate watchA watchB unit := by
  intro clause
  intro unit_cert
  exact ay_wlb_conj_intro
    (AyWLBClause watchA watchB unit)
    (AyWLBUnitCertificate watchA watchB unit)
    clause
    unit_cert

theorem ay_wlb_propagation_result_from_certificate
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWLBAbstractUnitCertificate watchA watchB unit ->
    AyWLBPropagationResult unit := by
  intro cert
  exact cert unit
    (fun clause unit_cert =>
      unit_cert unit
        (fun notA tail =>
          tail unit
            (fun notB _hunit =>
              ay_wlb_unit_discovery_sound watchA watchB unit
                clause notA notB)))

theorem ay_wlb_watched_propagation_matches_abstract
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWLBWatchedClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    AyWLBAbstractUnitCertificate watchA watchB unit := by
  intro watched_clause
  intro notA
  intro notB
  exact ay_wlb_abstract_unit_certificate_intro
    watchA
    watchB
    unit
    (ay_wlb_clause_to_abstract watchA watchB unit watched_clause)
    (ay_wlb_unit_certificate_intro
      watchA
      watchB
      unit
      notA
      notB
      (ay_wlb_unit_discovery_sound watchA watchB unit
        watched_clause notA notB))

theorem ay_wlb_watched_bcp_propagates_unit
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWLBWatchedClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    AyWLBPropagationResult unit := by
  intro watched_clause
  intro notA
  intro notB
  exact ay_wlb_propagation_result_from_certificate watchA watchB unit
    (ay_wlb_watched_propagation_matches_abstract
      watchA watchB unit watched_clause notA notB)
