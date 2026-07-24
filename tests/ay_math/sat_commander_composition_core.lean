-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained commander composition kernels.
-- This deliberately keeps the abstraction small and checker-friendly.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

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

def AyCommanderGroup2Cnf (x : Prop) (y : Prop) (cmd : Prop) :=
  AyConj
    (AyDisj (Not x) (Not y))
    (AyConj
      (AyDisj (Not x) cmd)
      (AyDisj (Not y) cmd))

def AyCommanderSplit2x2Cnf
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyConj
    (AyCommanderGroup2Cnf a b cmdAB)
    (AyConj
      (AyCommanderGroup2Cnf c d cmdCD)
      (AyDisj (Not cmdAB) (Not cmdCD)))

def AyTwoCommanderSplitsCnf
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (e : Prop) (f : Prop) (g : Prop) (h : Prop)
    (cmdEF : Prop) (cmdGH : Prop) :=
  AyConj
    (AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD)
    (AyCommanderSplit2x2Cnf e f g h cmdEF cmdGH)

theorem ay_commander_split_2x2_ab_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD ->
    a -> b -> False := by
  intro encoded
  intro ha
  intro hb
  exact encoded False
    (fun groupAB _tail =>
      groupAB False
        (fun ab_clause _guards =>
          ay_pair_clause_forbids_both a b ab_clause ha hb))

theorem ay_commander_split_2x2_ac_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD ->
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
                          commander_amo False
                            (fun not_cmdAB =>
                              not_cmdAB
                                (ay_guard_clause_implies_commander
                                  a cmdAB a_to_cmd ha))
                            (fun not_cmdCD =>
                              not_cmdCD
                                (ay_guard_clause_implies_commander
                                  c cmdCD c_to_cmd hc))))))))

theorem ay_two_commander_splits_first_local_pair_sound
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (e : Prop) (f : Prop) (g : Prop) (h : Prop)
    (cmdEF : Prop) (cmdGH : Prop) :
    AyTwoCommanderSplitsCnf
      a b c d cmdAB cmdCD e f g h cmdEF cmdGH ->
    a -> b -> False := by
  intro composed
  intro ha
  intro hb
  exact composed False
    (fun first_split _second_split =>
      ay_commander_split_2x2_ab_forbids
        a b c d cmdAB cmdCD first_split ha hb)

theorem ay_two_commander_splits_first_cross_pair_sound
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (e : Prop) (f : Prop) (g : Prop) (h : Prop)
    (cmdEF : Prop) (cmdGH : Prop) :
    AyTwoCommanderSplitsCnf
      a b c d cmdAB cmdCD e f g h cmdEF cmdGH ->
    a -> c -> False := by
  intro composed
  intro ha
  intro hc
  exact composed False
    (fun first_split _second_split =>
      ay_commander_split_2x2_ac_forbids
        a b c d cmdAB cmdCD first_split ha hc)

theorem ay_two_commander_splits_second_local_pair_sound
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (e : Prop) (f : Prop) (g : Prop) (h : Prop)
    (cmdEF : Prop) (cmdGH : Prop) :
    AyTwoCommanderSplitsCnf
      a b c d cmdAB cmdCD e f g h cmdEF cmdGH ->
    e -> f -> False := by
  intro composed
  intro he
  intro hf
  exact composed False
    (fun _first_split second_split =>
      ay_commander_split_2x2_ab_forbids
        e f g h cmdEF cmdGH second_split he hf)

theorem ay_two_commander_splits_second_cross_pair_sound
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (e : Prop) (f : Prop) (g : Prop) (h : Prop)
    (cmdEF : Prop) (cmdGH : Prop) :
    AyTwoCommanderSplitsCnf
      a b c d cmdAB cmdCD e f g h cmdEF cmdGH ->
    e -> g -> False := by
  intro composed
  intro he
  intro hg
  exact composed False
    (fun _first_split second_split =>
      ay_commander_split_2x2_ac_forbids
        e f g h cmdEF cmdGH second_split he hg)
