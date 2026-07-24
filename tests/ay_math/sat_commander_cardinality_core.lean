-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained commander/split cardinality kernels for SAT-COMP math work.
-- Church encodings keep the package independent of staged imports.

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

def AyCommanderGroup2Cnf (x : Prop) (y : Prop) (cmd : Prop) :=
  AyConj
    (AyDisj (Not x) (Not y))
    (AyConj
      (AyDisj (Not x) cmd)
      (AyDisj (Not y) cmd))

def AyCommanderGroup2Sound (x : Prop) (y : Prop) (cmd : Prop) :=
  AyConj
    (x -> y -> False)
    (AyConj (x -> cmd) (y -> cmd))

def AyCommanderSplit2x2Cnf
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyConj
    (AyCommanderGroup2Cnf a b cmdAB)
    (AyConj
      (AyCommanderGroup2Cnf c d cmdCD)
      (AyDisj (Not cmdAB) (Not cmdCD)))

def AyAtMostOne4
    (a : Prop) (b : Prop) (c : Prop) (d : Prop) :=
  AyConj
    (a -> b -> False)
    (AyConj
      (a -> c -> False)
      (AyConj
        (a -> d -> False)
        (AyConj
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False)))))

theorem ay_amo4_intro
    (a : Prop) (b : Prop) (c : Prop) (d : Prop) :
    (a -> b -> False) ->
    (a -> c -> False) ->
    (a -> d -> False) ->
    (b -> c -> False) ->
    (b -> d -> False) ->
    (c -> d -> False) ->
    AyAtMostOne4 a b c d := by
  intro ab
  intro ac
  intro ad
  intro bc
  intro bd
  intro cd
  intro result
  intro build
  exact build ab
    (ay_conj_intro
      (a -> c -> False)
      (AyConj
        (a -> d -> False)
        (AyConj
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False))))
      ac
      (ay_conj_intro
        (a -> d -> False)
        (AyConj
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False)))
        ad
        (ay_conj_intro
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False))
          bc
          (ay_conj_intro
            (b -> d -> False)
            (c -> d -> False)
            bd
            cd))))

theorem ay_commander_cross_forbids
    (left : Prop) (right : Prop)
    (cmdLeft : Prop) (cmdRight : Prop) :
    (left -> cmdLeft) ->
    (right -> cmdRight) ->
    AyDisj (Not cmdLeft) (Not cmdRight) ->
    left -> right -> False := by
  intro left_to_cmd
  intro right_to_cmd
  intro commander_amo
  intro hleft
  intro hright
  exact ay_pair_clause_forbids_both cmdLeft cmdRight commander_amo
    (left_to_cmd hleft)
    (right_to_cmd hright)

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

theorem ay_commander_split_2x2_cd_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD ->
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

theorem ay_commander_split_2x2_ad_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD ->
    a -> d -> False := by
  intro encoded
  intro ha
  intro hd
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
                        (fun _c_to_cmd d_to_cmd =>
                          commander_amo False
                            (fun not_cmdAB =>
                              not_cmdAB
                                (ay_guard_clause_implies_commander
                                  a cmdAB a_to_cmd ha))
                            (fun not_cmdCD =>
                              not_cmdCD
                                (ay_guard_clause_implies_commander
                                  d cmdCD d_to_cmd hd))))))))

theorem ay_commander_split_2x2_bc_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD ->
    b -> c -> False := by
  intro encoded
  intro hb
  intro hc
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
                        (fun c_to_cmd _d_to_cmd =>
                          commander_amo False
                            (fun not_cmdAB =>
                              not_cmdAB
                                (ay_guard_clause_implies_commander
                                  b cmdAB b_to_cmd hb))
                            (fun not_cmdCD =>
                              not_cmdCD
                                (ay_guard_clause_implies_commander
                                  c cmdCD c_to_cmd hc))))))))

theorem ay_commander_split_2x2_bd_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD ->
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
                          commander_amo False
                            (fun not_cmdAB =>
                              not_cmdAB
                                (ay_guard_clause_implies_commander
                                  b cmdAB b_to_cmd hb))
                            (fun not_cmdCD =>
                              not_cmdCD
                                (ay_guard_clause_implies_commander
                                  d cmdCD d_to_cmd hd))))))))
