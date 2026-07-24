-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for equivalence substitution inside commander
-- encoding guard clauses. The package is self-contained and uses Church
-- encodings, matching the SAT-COMP-facing theorem style.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquiv (p : Prop) (q : Prop) :=
  AyConj (p -> q) (q -> p)

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

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_equiv_forward
    (p : Prop) (q : Prop) :
    AyEquiv p q -> p -> q := by
  intro equiv
  exact equiv (p -> q) (fun forward _backward => forward)

theorem ay_equiv_backward
    (p : Prop) (q : Prop) :
    AyEquiv p q -> q -> p := by
  intro equiv
  exact equiv (q -> p) (fun _forward backward => backward)

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

theorem ay_equiv_pair_clause_forbids_substituted_left
    (lit : Prop) (litSubst : Prop) (other : Prop) :
    AyEquiv lit litSubst ->
    AyDisj (Not lit) (Not other) ->
    litSubst -> other -> False := by
  intro lit_equiv_subst
  intro pair_clause
  intro hsubst
  intro hother
  exact ay_pair_clause_forbids_both lit other pair_clause
    (ay_equiv_backward lit litSubst lit_equiv_subst hsubst)
    hother

theorem ay_equiv_guard_implies_commander_substituted
    (lit : Prop) (litSubst : Prop) (commander : Prop) :
    AyEquiv lit litSubst ->
    AyDisj (Not lit) commander ->
    litSubst -> commander := by
  intro lit_equiv_subst
  intro guard
  intro hsubst
  exact ay_guard_clause_implies_commander lit commander guard
    (ay_equiv_backward lit litSubst lit_equiv_subst hsubst)

theorem ay_commander_group2_sound
    (x : Prop) (y : Prop) (cmd : Prop) :
    AyCommanderGroup2Cnf x y cmd ->
    AyConj
      (x -> y -> False)
      (AyConj (x -> cmd) (y -> cmd)) :=
  fun group result build =>
    group result
      (fun pair_clause guards =>
        guards result
          (fun x_guard y_guard =>
            build
              (ay_pair_clause_forbids_both x y pair_clause)
              (ay_conj_intro
                (x -> cmd)
                (y -> cmd)
                (ay_guard_clause_implies_commander x cmd x_guard)
                (ay_guard_clause_implies_commander y cmd y_guard))))

theorem ay_equiv_commander_group2_sound
    (x : Prop) (xSubst : Prop) (y : Prop) (cmd : Prop) :
    AyEquiv x xSubst ->
    AyCommanderGroup2Cnf x y cmd ->
    AyConj
      (xSubst -> y -> False)
      (AyConj (xSubst -> cmd) (y -> cmd)) :=
  fun x_equiv_subst group result build =>
    group result
      (fun pair_clause guards =>
        guards result
          (fun x_guard y_guard =>
            build
              (ay_equiv_pair_clause_forbids_substituted_left
                x xSubst y x_equiv_subst pair_clause)
              (ay_conj_intro
                (xSubst -> cmd)
                (y -> cmd)
                (ay_equiv_guard_implies_commander_substituted
                  x xSubst cmd x_equiv_subst x_guard)
                (ay_guard_clause_implies_commander y cmd y_guard))))

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

theorem ay_amo4_substitute_left
    (a : Prop) (aSubst : Prop)
    (b : Prop) (c : Prop) (d : Prop) :
    AyEquiv a aSubst ->
    AyAtMostOne4 a b c d ->
    AyAtMostOne4 aSubst b c d := by
  intro a_equiv_subst
  intro amo
  exact amo (AyAtMostOne4 aSubst b c d)
    (fun ab tail =>
      tail (AyAtMostOne4 aSubst b c d)
        (fun ac tail2 =>
          tail2 (AyAtMostOne4 aSubst b c d)
            (fun ad tail3 =>
              tail3 (AyAtMostOne4 aSubst b c d)
                (fun bc tail4 =>
                  tail4 (AyAtMostOne4 aSubst b c d)
                    (fun bd cd =>
                      ay_amo4_intro aSubst b c d
                        (fun haSubst hb =>
                          ab
                            (ay_equiv_backward
                              a aSubst a_equiv_subst haSubst)
                            hb)
                        (fun haSubst hc =>
                          ac
                            (ay_equiv_backward
                              a aSubst a_equiv_subst haSubst)
                            hc)
                        (fun haSubst hd =>
                          ad
                            (ay_equiv_backward
                              a aSubst a_equiv_subst haSubst)
                            hd)
                        bc
                        bd
                        cd)))))

theorem ay_equiv_commander_amo_skeleton_preserved
    (a : Prop) (aSubst : Prop)
    (b : Prop) (c : Prop) (d : Prop) :
    AyEquiv a aSubst ->
    AyAtMostOne4 a b c d ->
    AyAtMostOne4 aSubst b c d := by
  intro a_equiv_subst
  exact ay_amo4_substitute_left a aSubst b c d a_equiv_subst

theorem ay_equiv_commander_guard_and_amo_pair
    (a : Prop) (aSubst : Prop)
    (b : Prop) (c : Prop) (d : Prop)
    (cmd : Prop) :
    AyEquiv a aSubst ->
    AyCommanderGroup2Cnf a b cmd ->
    AyAtMostOne4 a b c d ->
    AyConj
      (AyConj
        (aSubst -> b -> False)
        (AyConj (aSubst -> cmd) (b -> cmd)))
      (AyAtMostOne4 aSubst b c d) :=
  fun a_equiv_subst group amo =>
    ay_conj_intro
      (AyConj
        (aSubst -> b -> False)
        (AyConj (aSubst -> cmd) (b -> cmd)))
      (AyAtMostOne4 aSubst b c d)
      (ay_equiv_commander_group2_sound
        a aSubst b cmd a_equiv_subst group)
      (ay_amo4_substitute_left
        a aSubst b c d a_equiv_subst amo)
