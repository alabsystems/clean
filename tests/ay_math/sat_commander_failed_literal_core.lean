-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained commander cardinality plus failed-literal unit kernels.
-- Extra unit facts are modeled as Church-conjoined side conditions.

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

def AyFailedLiteralUnits (u : Prop) (v : Prop) :=
  AyConj u v

def AyCommanderSplitWithFailedUnits
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (unitA : Prop) (unitC : Prop) :=
  AyConj
    (AyCommanderSplit2x2Cnf a b c d cmdAB cmdCD)
    (AyFailedLiteralUnits unitA unitC)

theorem ay_commander_failed_units_preserve_ab_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (unitA : Prop) (unitC : Prop) :
    AyCommanderSplitWithFailedUnits a b c d cmdAB cmdCD unitA unitC ->
    a -> b -> False := by
  intro strengthened
  intro ha
  intro hb
  exact strengthened False
    (fun split _units =>
      split False
        (fun groupAB _tail =>
          groupAB False
            (fun ab_clause _guards =>
              ay_pair_clause_forbids_both a b ab_clause ha hb)))

theorem ay_commander_failed_units_preserve_ac_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop)
    (unitA : Prop) (unitC : Prop) :
    AyCommanderSplitWithFailedUnits a b c d cmdAB cmdCD unitA unitC ->
    a -> c -> False := by
  intro strengthened
  intro ha
  intro hc
  exact strengthened False
    (fun split _units =>
      split False
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
                                      c cmdCD c_to_cmd hc)))))))))

theorem ay_failed_literal_units_project_left
    (u : Prop) (v : Prop) :
    AyFailedLiteralUnits u v -> u := by
  intro units
  exact units u (fun hu _hv => hu)

theorem ay_failed_literal_units_project_right
    (u : Prop) (v : Prop) :
    AyFailedLiteralUnits u v -> v := by
  intro units
  exact units v (fun _hu hv => hv)

theorem ay_commander_failed_units_cross_conflict
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderSplitWithFailedUnits a b c d cmdAB cmdCD a c ->
    False := by
  intro strengthened
  exact strengthened False
    (fun split units =>
      ay_commander_failed_units_preserve_ac_forbids
        a b c d cmdAB cmdCD a c
        (fun result build => build split units)
        (ay_failed_literal_units_project_left a c units)
        (ay_failed_literal_units_project_right a c units))
