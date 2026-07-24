-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained commander/BVE interaction kernels.
-- BVE over a commander auxiliary is modeled as resolving a guard
-- `(not lit or cmd)` with a commander AMO clause `(not cmd or not other)`.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_pair_clause_forbids_both
    (p : Prop) (q : Prop) :
    AyDisj (Not p) (Not q) -> p -> q -> False := by
  intro pair_clause
  intro hp
  intro hq
  exact pair_clause False
    (fun not_p => not_p hp)
    (fun not_q => not_q hq)

theorem ay_guard_clause_implies_commander
    (lit : Prop) (commander : Prop) :
    AyDisj (Not lit) commander -> lit -> commander := by
  intro guard
  intro hlit
  exact guard commander
    (fun not_lit => False.elim (not_lit hlit))
    (fun hcommander => hcommander)

theorem ay_commander_aux_bve_projected_pair_forbids
    (lit : Prop) (other : Prop) (commander : Prop) :
    AyDisj (Not lit) commander ->
    AyDisj (Not commander) (Not other) ->
    lit -> other -> False := by
  intro guard
  intro commander_amo
  intro hlit
  intro hother
  exact commander_amo False
    (fun not_commander =>
      not_commander
        (ay_guard_clause_implies_commander lit commander guard hlit))
    (fun not_other => not_other hother)

def AyCommanderGroup2Cnf (x : Prop) (y : Prop) (cmd : Prop) :=
  AyConj
    (AyDisj (Not x) (Not y))
    (AyConj
      (AyDisj (Not x) cmd)
      (AyDisj (Not y) cmd))

def AyCommanderBveProjected2x2
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyConj
    (AyCommanderGroup2Cnf a b cmdAB)
    (AyConj
      (AyCommanderGroup2Cnf c d cmdCD)
      (AyDisj (Not cmdAB) (Not cmdCD)))

theorem ay_commander_bve_preserves_local_pair_ab
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    a -> b -> False := by
  intro encoded
  intro ha
  intro hb
  exact encoded False
    (fun groupAB _tail =>
      groupAB False
        (fun ab_clause _guards =>
          ay_pair_clause_forbids_both a b ab_clause ha hb))

theorem ay_commander_bve_preserves_local_pair_cd
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    c -> d -> False := by
  intro encoded
  intro hc
  intro hd
  exact encoded False
    (fun _groupAB tail =>
      tail False
        (fun groupCD _commander_amo =>
          groupCD False
            (fun cd_clause _guards =>
              ay_pair_clause_forbids_both c d cd_clause hc hd)))

theorem ay_commander_bve_projects_a_c_pair
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    a -> c -> False := by
  intro encoded
  intro ha
  intro hc
  exact encoded False
    (fun groupAB tail =>
      tail False
        (fun groupCD commander_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun a_to_cmd _b_to_cmd =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun c_to_cmd _d_to_cmd =>
                          ay_commander_aux_bve_projected_pair_forbids
                            a cmdCD cmdAB
                            a_to_cmd commander_amo
                            ha
                            (ay_guard_clause_implies_commander
                              c cmdCD c_to_cmd hc))))))))

theorem ay_commander_bve_projects_b_d_pair
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    b -> d -> False := by
  intro encoded
  intro hb
  intro hd
  exact encoded False
    (fun groupAB tail =>
      tail False
        (fun groupCD commander_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun _a_to_cmd b_to_cmd =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun _c_to_cmd d_to_cmd =>
                          ay_commander_aux_bve_projected_pair_forbids
                            b cmdCD cmdAB
                            b_to_cmd commander_amo
                            hb
                            (ay_guard_clause_implies_commander
                              d cmdCD d_to_cmd hd))))))))

def AyProjectedAmoSkeleton4 (a : Prop) (b : Prop) (c : Prop) (d : Prop) :=
  AyConj
    (a -> b -> False)
    (AyConj
      (c -> d -> False)
      (AyConj
        (a -> c -> False)
        (b -> d -> False)))

theorem ay_commander_bve_preserves_projected_amo_skeleton
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    AyProjectedAmoSkeleton4 a b c d := by
  intro encoded
  intro result
  intro build
  exact build
    (ay_commander_bve_preserves_local_pair_ab
      a b c d cmdAB cmdCD encoded)
    (ay_conj_intro
      (c -> d -> False)
      (AyConj (a -> c -> False) (b -> d -> False))
      (ay_commander_bve_preserves_local_pair_cd
        a b c d cmdAB cmdCD encoded)
      (ay_conj_intro
        (a -> c -> False)
        (b -> d -> False)
        (ay_commander_bve_projects_a_c_pair
          a b c d cmdAB cmdCD encoded)
        (ay_commander_bve_projects_b_d_pair
          a b c d cmdAB cmdCD encoded)))
