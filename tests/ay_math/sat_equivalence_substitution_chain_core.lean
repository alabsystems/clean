-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for composing SCC/equivalence substitutions.
-- The package is self-contained and uses Church encodings, matching the
-- SAT-COMP-facing theorem style in sat_comp_transform_core.lean.

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyEquiv (p : Prop) (q : Prop) :=
  AyConj (p -> q) (q -> p)

def AyTwoClauseContext
    (atom : Prop) (leftClauseRest : Prop) (rightClauseRest : Prop) :=
  AyConj atom (AyConj leftClauseRest (AyConj atom rightClauseRest))

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

theorem ay_equiv_trans
    (p : Prop) (q : Prop) (r : Prop) :
    AyEquiv p q ->
    AyEquiv q r ->
    AyEquiv p r := by
  intro p_equiv_q
  intro q_equiv_r
  exact ay_conj_intro
    (p -> r)
    (r -> p)
    (fun hp =>
      ay_equiv_forward q r q_equiv_r
        (ay_equiv_forward p q p_equiv_q hp))
    (fun hr =>
      ay_equiv_backward p q p_equiv_q
        (ay_equiv_backward q r q_equiv_r hr))

theorem ay_equivalence_substitution_forward
    (p : Prop) (q : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyTwoClauseContext p leftClauseRest rightClauseRest ->
    AyTwoClauseContext q leftClauseRest rightClauseRest := by
  intro p_equiv_q
  intro original
  intro result
  intro build
  exact original result
    (fun hp tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hpAgain hright =>
              build
                (ay_equiv_forward p q p_equiv_q hp)
                (ay_conj_intro leftClauseRest (AyConj q rightClauseRest)
                  hleft
                  (ay_conj_intro q rightClauseRest
                    (ay_equiv_forward p q p_equiv_q hp)
                    hright)))))

theorem ay_equivalence_substitution_backward
    (p : Prop) (q : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyTwoClauseContext q leftClauseRest rightClauseRest ->
    AyTwoClauseContext p leftClauseRest rightClauseRest := by
  intro p_equiv_q
  intro substituted
  intro result
  intro build
  exact substituted result
    (fun hq tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hqAgain hright =>
              build
                (ay_equiv_backward p q p_equiv_q hq)
                (ay_conj_intro leftClauseRest (AyConj p rightClauseRest)
                  hleft
                  (ay_conj_intro p rightClauseRest
                    (ay_equiv_backward p q p_equiv_q hq)
                    hright)))))

theorem ay_equivalence_substitution_chain_forward
    (p : Prop) (q : Prop) (r : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyEquiv q r ->
    AyTwoClauseContext p leftClauseRest rightClauseRest ->
    AyTwoClauseContext r leftClauseRest rightClauseRest := by
  intro p_equiv_q
  intro q_equiv_r
  intro pContext
  exact ay_equivalence_substitution_forward q r
    leftClauseRest rightClauseRest q_equiv_r
    (ay_equivalence_substitution_forward p q
      leftClauseRest rightClauseRest p_equiv_q pContext)

theorem ay_equivalence_substitution_chain_backward
    (p : Prop) (q : Prop) (r : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyEquiv q r ->
    AyTwoClauseContext r leftClauseRest rightClauseRest ->
    AyTwoClauseContext p leftClauseRest rightClauseRest := by
  intro p_equiv_q
  intro q_equiv_r
  intro rContext
  exact ay_equivalence_substitution_backward p q
    leftClauseRest rightClauseRest p_equiv_q
    (ay_equivalence_substitution_backward q r
      leftClauseRest rightClauseRest q_equiv_r rContext)

theorem ay_equivalence_substitution_chain_equisat
    (p : Prop) (q : Prop) (r : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyEquiv q r ->
    AyEquisat
      (AyTwoClauseContext p leftClauseRest rightClauseRest)
      (AyTwoClauseContext r leftClauseRest rightClauseRest) := by
  intro p_equiv_q
  intro q_equiv_r
  exact ay_conj_intro
    (AyTwoClauseContext p leftClauseRest rightClauseRest ->
      AyTwoClauseContext r leftClauseRest rightClauseRest)
    (AyTwoClauseContext r leftClauseRest rightClauseRest ->
      AyTwoClauseContext p leftClauseRest rightClauseRest)
    (ay_equivalence_substitution_chain_forward
      p q r leftClauseRest rightClauseRest p_equiv_q q_equiv_r)
    (ay_equivalence_substitution_chain_backward
      p q r leftClauseRest rightClauseRest p_equiv_q q_equiv_r)

theorem ay_equivalence_substitution_chain_forward_via_trans
    (p : Prop) (q : Prop) (r : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyEquiv q r ->
    AyTwoClauseContext p leftClauseRest rightClauseRest ->
    AyTwoClauseContext r leftClauseRest rightClauseRest := by
  intro p_equiv_q
  intro q_equiv_r
  exact ay_equivalence_substitution_forward p r
    leftClauseRest rightClauseRest
    (ay_equiv_trans p q r p_equiv_q q_equiv_r)

theorem ay_equivalence_substitution_chain_backward_via_trans
    (p : Prop) (q : Prop) (r : Prop)
    (leftClauseRest : Prop) (rightClauseRest : Prop) :
    AyEquiv p q ->
    AyEquiv q r ->
    AyTwoClauseContext r leftClauseRest rightClauseRest ->
    AyTwoClauseContext p leftClauseRest rightClauseRest := by
  intro p_equiv_q
  intro q_equiv_r
  exact ay_equivalence_substitution_backward p r
    leftClauseRest rightClauseRest
    (ay_equiv_trans p q r p_equiv_q q_equiv_r)
